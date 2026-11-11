import Mathlib

/-! A variable-coefficient energy estimate for the high-order bootstrap. -/

noncomputable section
open Set MeasureTheory
open scoped Interval
namespace SingularClosure

private theorem linear_primitive_continuousOn_Icc
    {f : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hf : ContinuousOn f (Icc 0 T)) :
    ContinuousOn (fun t : ℝ => ∫ s in (0 : ℝ)..t, f s) (Icc 0 T) := by
  have hi : IntervalIntegrable f volume 0 T :=
    hf.intervalIntegrable_of_Icc hT
  simpa only [uIcc_of_le hT] using
    (intervalIntegral.continuousOn_primitive_interval' hi
      (left_mem_uIcc : (0 : ℝ) ∈ uIcc 0 T))

private theorem linear_primitive_hasDerivAt_Ioo
    {f : ℝ → ℝ} {T t : ℝ}
    (hf : ContinuousOn f (Icc 0 T)) (ht : t ∈ Ioo 0 T) :
    HasDerivAt (fun x : ℝ => ∫ s in (0 : ℝ)..x, f s) (f t) t := by
  have hi : IntervalIntegrable f volume 0 t :=
    (hf.mono (Icc_subset_Icc le_rfl ht.2.le)).intervalIntegrable_of_Icc ht.1.le
  have hm : StronglyMeasurableAtFilter f (nhds t) volume :=
    ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo
      (hf.mono Ioo_subset_Icc_self) t ht
  exact intervalIntegral.integral_hasDerivAt_right hi hm
    (hf.continuousAt (Icc_mem_nhds ht.1 ht.2))

theorem linear_dissipation_integrating_factor_antitone
    {y z d a : ℝ → ℝ} {ν T : ℝ}
    (hT : 0 ≤ T) (hν : 0 ≤ ν)
    (hy : ContinuousOn y (Icc 0 T))
    (hz : ContinuousOn z (Icc 0 T))
    (ha : ContinuousOn a (Icc 0 T))
    (ha_nonneg : ∀ t ∈ Icc 0 T, 0 ≤ a t)
    (hderiv : ∀ t ∈ Ioo 0 T, HasDerivAt y (d t) t)
    (hlinear : ∀ t ∈ Ioo 0 T, d t + ν * (z t) ^ 2 ≤ a t * y t) :
    AntitoneOn
      (fun t : ℝ =>
        (y t + ν * ∫ s in (0 : ℝ)..t, (z s) ^ 2) *
          Real.exp (-(∫ s in (0 : ℝ)..t, a s))) (Icc 0 T) := by
  let A : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, a s
  let Z : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, (z s) ^ 2
  let Q : ℝ → ℝ := fun t => y t + ν * Z t
  let F : ℝ → ℝ := fun t => Q t * Real.exp (-A t)
  have hAc : ContinuousOn A (Icc 0 T) := linear_primitive_continuousOn_Icc hT ha
  have hZc : ContinuousOn Z (Icc 0 T) :=
    linear_primitive_continuousOn_Icc hT (hz.pow 2)
  have hFc : ContinuousOn F (Icc 0 T) := by
    change ContinuousOn (fun t => (y t + ν * Z t) * Real.exp (-A t)) (Icc 0 T)
    exact (hy.add (continuousOn_const.mul hZc)).mul
      (Real.continuous_exp.comp_continuousOn hAc.neg)
  have hFd : ∀ t ∈ Ioo 0 T, HasDerivAt F
      (((d t + ν * (z t) ^ 2) - a t * Q t) * Real.exp (-A t)) t := by
    intro t ht
    have hAd : HasDerivAt A (a t) t := linear_primitive_hasDerivAt_Ioo ha ht
    have hZd : HasDerivAt Z ((z t) ^ 2) t :=
      linear_primitive_hasDerivAt_Ioo (hz.pow 2) ht
    have hQd : HasDerivAt Q (d t + ν * (z t) ^ 2) t :=
      (hderiv t ht).add (hZd.const_mul ν)
    have hraw : HasDerivAt F
        ((d t + ν * (z t) ^ 2) * Real.exp (-A t) +
          Q t * (Real.exp (-A t) * (-a t))) t := hQd.mul hAd.neg.exp
    convert hraw using 1 <;> ring
  have hFd_nonpos : ∀ t ∈ Ioo 0 T,
      ((d t + ν * (z t) ^ 2) - a t * Q t) * Real.exp (-A t) ≤ 0 := by
    intro t ht
    have hZ_nonneg : 0 ≤ Z t :=
      intervalIntegral.integral_nonneg_of_forall ht.1.le (fun s => sq_nonneg (z s))
    have hcorr : 0 ≤ a t * (ν * Z t) :=
      mul_nonneg (ha_nonneg t ⟨ht.1.le, ht.2.le⟩) (mul_nonneg hν hZ_nonneg)
    have hcoeff : (d t + ν * (z t) ^ 2) - a t * Q t ≤ 0 := by
      dsimp [Q]
      nlinarith only [hlinear t ht, hcorr]
    exact mul_nonpos_of_nonpos_of_nonneg hcoeff (Real.exp_pos _).le
  change AntitoneOn F (Icc 0 T)
  apply antitoneOn_of_deriv_nonpos (convex_Icc (0 : ℝ) T) hFc
  · intro t ht
    have ht' : t ∈ Ioo 0 T := by simpa only [interior_Icc] using ht
    exact (hFd t ht').differentiableAt.differentiableWithinAt
  · intro t ht
    have ht' : t ∈ Ioo 0 T := by simpa only [interior_Icc] using ht
    rw [(hFd t ht').deriv]
    exact hFd_nonpos t ht'

theorem LINEAR_ENERGY_OF_COEFFICIENT_BUDGET
    {y z d a : ℝ → ℝ} {ν T M y₀ : ℝ}
    (hν : 0 ≤ ν) (hT : 0 ≤ T)
    (hy : ContinuousOn y (Icc 0 T))
    (hz : ContinuousOn z (Icc 0 T))
    (ha : ContinuousOn a (Icc 0 T))
    (hy_nonneg : ∀ t ∈ Icc 0 T, 0 ≤ y t)
    (ha_nonneg : ∀ t ∈ Icc 0 T, 0 ≤ a t)
    (h_initial : y 0 ≤ y₀)
    (hderiv : ∀ t ∈ Ioo 0 T, HasDerivAt y (d t) t)
    (hlinear : ∀ t ∈ Ioo 0 T, d t + ν * (z t) ^ 2 ≤ a t * y t)
    (hbudget : (∫ s in (0 : ℝ)..T, a s) ≤ M) :
    ∀ t ∈ Icc 0 T,
      y t + ν * (∫ s in (0 : ℝ)..t, (z s) ^ 2) ≤ y₀ * Real.exp M := by
  have hzero : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT⟩
  have hy₀ : 0 ≤ y₀ := (hy_nonneg 0 hzero).trans h_initial
  have hanti := linear_dissipation_integrating_factor_antitone
    hT hν hy hz ha ha_nonneg hderiv hlinear
  have hi : IntervalIntegrable a volume 0 T := ha.intervalIntegrable_of_Icc hT
  intro t ht
  let A : ℝ := ∫ s in (0 : ℝ)..t, a s
  let Q : ℝ := y t + ν * (∫ s in (0 : ℝ)..t, (z s) ^ 2)
  have hfactor : Q * Real.exp (-A) ≤ y₀ := by
    have h := hanti hzero ht ht.1
    have h' : Q * Real.exp (-A) ≤ y 0 := by
      simpa only [A, Q, intervalIntegral.integral_same, mul_zero,
        add_zero, neg_zero, Real.exp_zero, mul_one] using h
    exact h'.trans h_initial
  have hcancel : Real.exp (-A) * Real.exp A = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hQ : Q ≤ y₀ * Real.exp A := by
    calc
      Q = (Q * Real.exp (-A)) * Real.exp A := by rw [mul_assoc, hcancel, mul_one]
      _ ≤ _ := mul_le_mul_of_nonneg_right hfactor (Real.exp_pos _).le
  have hA : A ≤ M := by
    have hmono : (∫ s in (0 : ℝ)..t, a s) ≤ ∫ s in (0 : ℝ)..T, a s := by
      apply intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2 _ hi
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      exact ha_nonneg s ⟨hs.1.le, hs.2⟩
    exact hmono.trans hbudget
  exact hQ.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hA) hy₀)

end SingularClosure

