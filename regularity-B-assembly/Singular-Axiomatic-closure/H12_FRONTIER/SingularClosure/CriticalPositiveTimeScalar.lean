import SingularClosure.CubicBudget

/-! Positive-time smoothing for the scalar cubic differential inequality.
The initial seed is selected by the actual square integral on [0,τ]. -/

set_option autoImplicit false
set_option Elab.async true

noncomputable section

open Set MeasureTheory
open scoped Interval

namespace SingularClosure

theorem continuous_exists_point_le_integral_bound
    {f : ℝ → ℝ} {τ M : ℝ} (hτ : 0 < τ)
    (hf : ContinuousOn f (Icc 0 τ))
    (hbudget : (∫ t in (0 : ℝ)..τ, f t) ≤ M) :
    ∃ s ∈ Icc 0 τ, f s ≤ M / τ := by
  obtain ⟨s, hs, hmin⟩ := isCompact_Icc.exists_isMinOn
    (nonempty_Icc.mpr hτ.le) hf
  refine ⟨s, hs, (le_div_iff₀ hτ).2 ?_⟩
  have hmono : (∫ t in (0 : ℝ)..τ, f s) ≤ ∫ t in (0 : ℝ)..τ, f t :=
    intervalIntegral.integral_mono_on hτ.le intervalIntegrable_const
      (hf.intervalIntegrable_of_Icc hτ.le) (fun _ ht => hmin ht)
  rw [intervalIntegral.integral_const] at hmono
  simp only [sub_zero, smul_eq_mul] at hmono
  nlinarith

theorem CUBIC_POSITIVE_TIME_ACCUMULATION
    {y z d : ℝ → ℝ} {ν κ T τ M : ℝ}
    (hν : 0 < ν) (hκ : 0 ≤ κ) (hτ : 0 < τ) (hτT : τ ≤ T) (hM : 0 ≤ M)
    (hy : ContinuousOn y (Icc 0 T))
    (hz : ContinuousOn z (Icc 0 T))
    (hd : ContinuousOn d (Icc 0 T))
    (hynonneg : ∀ t ∈ Icc 0 T, 0 ≤ y t)
    (hderiv : ∀ t ∈ Ioo 0 T, HasDerivAt y (d t) t)
    (hcubic : ∀ t ∈ Ioo 0 T, d t + ν * z t ^ 2 ≤ κ * y t ^ 3)
    (hbudget : (∫ t in (0 : ℝ)..T, y t ^ 2) ≤ M) :
    ∀ t ∈ Icc τ T,
      y t + ν * (∫ r in τ..t, z r ^ 2) ≤ Real.sqrt (M / τ) * Real.exp (κ * M) := by
  have hT : 0 ≤ T := hτ.le.trans hτT
  have hy2i : IntervalIntegrable (fun t => y t ^ 2) volume 0 T :=
    (hy.pow 2).intervalIntegrable_of_Icc hT
  have hτbudget : (∫ t in (0 : ℝ)..τ, y t ^ 2) ≤ M :=
    (intervalIntegral.integral_mono_interval le_rfl hτ.le hτT
      (Filter.Eventually.of_forall (fun t => sq_nonneg (y t))) hy2i).trans hbudget
  obtain ⟨s, hs, hseed⟩ := continuous_exists_point_le_integral_bound hτ
    ((hy.pow 2).mono (Icc_subset_Icc le_rfl hτT)) hτbudget
  have hsT : s ≤ T := hs.2.trans hτT
  have hmap : MapsTo (fun r : ℝ => r + s) (Icc 0 (T - s)) (Icc 0 T) := by
    intro r hr
    exact ⟨add_nonneg hr.1 hs.1, by dsimp; linarith [hr.2]⟩
  have hshift : ContinuousOn (fun r : ℝ => r + s) (Icc 0 (T - s)) := by fun_prop
  have hys : ContinuousOn (fun r => y (r + s)) (Icc 0 (T - s)) := hy.comp hshift hmap
  have hzs : ContinuousOn (fun r => z (r + s)) (Icc 0 (T - s)) := hz.comp hshift hmap
  have hds : ContinuousOn (fun r => d (r + s)) (Icc 0 (T - s)) := hd.comp hshift hmap
  have hysnonneg : ∀ r ∈ Icc 0 (T - s), 0 ≤ y (r + s) :=
    fun r hr => hynonneg (r + s) (hmap hr)
  have hseed' : y (0 + s) ≤ Real.sqrt (M / τ) := by
    rw [zero_add]
    exact (Real.le_sqrt (hynonneg s ⟨hs.1, hsT⟩) (div_nonneg hM hτ.le)).mpr hseed
  have hders : ∀ r ∈ Ioo 0 (T - s),
      HasDerivAt (fun x => y (x + s)) (d (r + s)) r := by
    intro r hr
    have hr' : r + s ∈ Ioo 0 T :=
      ⟨add_pos_of_pos_of_nonneg hr.1 hs.1, by linarith [hr.2]⟩
    simpa only [mul_one] using!
      (hderiv (r + s) hr').comp r ((hasDerivAt_id r).add_const s)
  have hcubics : ∀ r ∈ Ioo 0 (T - s),
      d (r + s) + ν * z (r + s) ^ 2 ≤ κ * y (r + s) ^ 3 := by
    intro r hr
    exact hcubic (r + s) ⟨add_pos_of_pos_of_nonneg hr.1 hs.1, by linarith [hr.2]⟩
  have hbudgets : (∫ r in (0 : ℝ)..(T - s), y (r + s) ^ 2) ≤ M := by
    rw [intervalIntegral.integral_comp_add_right (fun r => y r ^ 2) s,
      zero_add, sub_add_cancel]
    exact (intervalIntegral.integral_mono_interval hs.1 hsT le_rfl
      (Filter.Eventually.of_forall (fun t => sq_nonneg (y t))) hy2i).trans hbudget
  have hacc := CUBIC_ENERGY_OF_SQUARE_BUDGET hν hκ (sub_nonneg.mpr hsT) hM
    hys hzs hds hysnonneg hseed' hders hcubics hbudgets
  intro t ht
  have hst : s ≤ t := hs.2.trans ht.1
  have htt : t - s ∈ Icc 0 (T - s) :=
    ⟨sub_nonneg.mpr hst, sub_le_sub_right ht.2 s⟩
  have hacc' : y t + ν * (∫ r in s..t, z r ^ 2) ≤
      Real.sqrt (M / τ) * Real.exp (κ * M) := by
    have h := hacc (t - s) htt
    rw [intervalIntegral.integral_comp_add_right (fun r => z r ^ 2) s] at h
    simpa only [sub_add_cancel, zero_add] using h
  have hzi : IntervalIntegrable (fun r => z r ^ 2) volume s t :=
    ((hz.pow 2).mono (Icc_subset_Icc hs.1 ht.2)).intervalIntegrable_of_Icc hst
  have hmono : (∫ r in τ..t, z r ^ 2) ≤ ∫ r in s..t, z r ^ 2 :=
    intervalIntegral.integral_mono_interval hs.2 ht.1 le_rfl
      (Filter.Eventually.of_forall (fun r => sq_nonneg (z r))) hzi
  have hmul := mul_le_mul_of_nonneg_left hmono hν.le
  linarith

end SingularClosure
