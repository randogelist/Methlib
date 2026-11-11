import Mathlib

/-!
# A cubic differential inequality controlled by a square budget

This file contains only the scalar calculus edge of the NSE closure chain.
It has no PDE axiom and no assumed Gronwall conclusion.  The integrating
factor includes the accumulated dissipation, so the conclusion controls
the sum of the instantaneous energy and its dissipation integral.
-/

noncomputable section

open Set MeasureTheory
open scoped Interval

namespace SingularClosure

private theorem primitive_continuousOn_Icc
    {f : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hf : ContinuousOn f (Icc 0 T)) :
    ContinuousOn (fun t : ℝ => ∫ s in (0 : ℝ)..t, f s) (Icc 0 T) := by
  have hi : IntervalIntegrable f volume 0 T :=
    hf.intervalIntegrable_of_Icc hT
  simpa only [uIcc_of_le hT] using
    (intervalIntegral.continuousOn_primitive_interval' hi
      (left_mem_uIcc : (0 : ℝ) ∈ uIcc 0 T))

private theorem primitive_hasDerivAt_Ioo
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

/-- The integrating factor is antitone, including the endpoints.

The derivative bound is needed only in the open time interval.  No
derivative at the initial or terminal time is imposed. -/
theorem cubic_dissipation_integrating_factor_antitone
    {y z d : ℝ → ℝ} {ν κ T : ℝ}
    (hT : 0 ≤ T) (hν : 0 ≤ ν) (hκ : 0 ≤ κ)
    (hy : ContinuousOn y (Icc 0 T))
    (hz : ContinuousOn z (Icc 0 T))
    (hderiv : ∀ t ∈ Ioo 0 T, HasDerivAt y (d t) t)
    (hcubic : ∀ t ∈ Ioo 0 T, d t + ν * (z t) ^ 2 ≤ κ * (y t) ^ 3) :
    AntitoneOn
      (fun t : ℝ =>
        (y t + ν * ∫ s in (0 : ℝ)..t, (z s) ^ 2) *
          Real.exp ((-κ) * ∫ s in (0 : ℝ)..t, (y s) ^ 2))
      (Icc 0 T) := by
  let A : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, (y s) ^ 2
  let Z : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, (z s) ^ 2
  let Q : ℝ → ℝ := fun t => y t + ν * Z t
  let F : ℝ → ℝ := fun t => Q t * Real.exp ((-κ) * A t)
  have hAc : ContinuousOn A (Icc 0 T) :=
    primitive_continuousOn_Icc hT (hy.pow 2)
  have hZc : ContinuousOn Z (Icc 0 T) :=
    primitive_continuousOn_Icc hT (hz.pow 2)
  have hFc : ContinuousOn F (Icc 0 T) := by
    change ContinuousOn
      (fun t => (y t + ν * Z t) * Real.exp ((-κ) * A t)) (Icc 0 T)
    exact (hy.add (continuousOn_const.mul hZc)).mul
      ((continuousOn_const.mul hAc).exp)
  have hFd : ∀ t ∈ Ioo 0 T,
      HasDerivAt F
        (((d t + ν * (z t) ^ 2) - κ * (y t) ^ 2 * Q t) *
          Real.exp ((-κ) * A t)) t := by
    intro t ht
    have hAd : HasDerivAt A ((y t) ^ 2) t :=
      primitive_hasDerivAt_Ioo (hy.pow 2) ht
    have hZd : HasDerivAt Z ((z t) ^ 2) t :=
      primitive_hasDerivAt_Ioo (hz.pow 2) ht
    have hQd : HasDerivAt Q (d t + ν * (z t) ^ 2) t :=
      (hderiv t ht).add (hZd.const_mul ν)
    dsimp [F]
    convert hQd.mul ((hAd.const_mul (-κ)).exp) using 1 <;> ring
  have hFd_nonpos : ∀ t ∈ Ioo 0 T,
      ((d t + ν * (z t) ^ 2) - κ * (y t) ^ 2 * Q t) *
          Real.exp ((-κ) * A t) ≤ 0 := by
    intro t ht
    have hZ_nonneg : 0 ≤ Z t :=
      intervalIntegral.integral_nonneg_of_forall ht.1.le
        (fun s => sq_nonneg (z s))
    have hcorr : 0 ≤ κ * (y t) ^ 2 * (ν * Z t) :=
      mul_nonneg (mul_nonneg hκ (sq_nonneg (y t))) (mul_nonneg hν hZ_nonneg)
    have hcoeff : (d t + ν * (z t) ^ 2) - κ * (y t) ^ 2 * Q t ≤ 0 := by
      dsimp [Q]
      nlinarith only [hcubic t ht, hcorr]
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

/-- Endpoint 6, with an explicit initial upper bound `y₀`.

All analytic hypotheses concern the finite interval `[0,T]`.  The
continuity of `d` is retained in this endpoint's signature for the C¹
Galerkin interface, although the integrating-factor proof needs only the
stated pointwise derivative and differential inequality.

For the NSE application, `y = ‖∇u_N‖₂²`, `z = ‖Δu_N‖₂`, and
`κ = C / ν³`.  Thus `M` is exactly the square budget `∫ y²`.
-/
theorem CUBIC_ENERGY_OF_SQUARE_BUDGET
    {y z d : ℝ → ℝ} {ν κ T M y₀ : ℝ}
    (hν : 0 < ν) (hκ : 0 ≤ κ) (hT : 0 ≤ T) (hM : 0 ≤ M)
    (hy : ContinuousOn y (Icc 0 T))
    (hz : ContinuousOn z (Icc 0 T))
    (hd : ContinuousOn d (Icc 0 T))
    (hy_nonneg : ∀ t ∈ Icc 0 T, 0 ≤ y t)
    (h_initial : y 0 ≤ y₀)
    (hderiv : ∀ t ∈ Ioo 0 T, HasDerivAt y (d t) t)
    (hcubic : ∀ t ∈ Ioo 0 T, d t + ν * (z t) ^ 2 ≤ κ * (y t) ^ 3)
    (hbudget : (∫ s in (0 : ℝ)..T, (y s) ^ 2) ≤ M) :
    ∀ t ∈ Icc 0 T,
      y t + ν * (∫ s in (0 : ℝ)..t, (z s) ^ 2) ≤ y₀ * Real.exp (κ * M) := by
  have hzero : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT⟩
  have hy₀ : 0 ≤ y₀ := (hy_nonneg 0 hzero).trans h_initial
  have hanti := cubic_dissipation_integrating_factor_antitone
    hT hν.le hκ hy hz hderiv hcubic
  have hi : IntervalIntegrable (fun s => (y s) ^ 2) volume 0 T :=
    (hy.pow 2).intervalIntegrable_of_Icc hT
  intro t ht
  let A : ℝ := ∫ s in (0 : ℝ)..t, (y s) ^ 2
  let Q : ℝ := y t + ν * (∫ s in (0 : ℝ)..t, (z s) ^ 2)
  have hfactor : Q * Real.exp ((-κ) * A) ≤ y₀ := by
    have h := hanti hzero ht ht.1
    have h' : Q * Real.exp ((-κ) * A) ≤ y 0 := by
      simpa only [A, Q, intervalIntegral.integral_same, mul_zero,
        add_zero, Real.exp_zero, mul_one] using h
    exact h'.trans h_initial
  have hcancel : Real.exp ((-κ) * A) * Real.exp (κ * A) = 1 := by
    rw [← Real.exp_add]
    have hzero_exp : (-κ) * A + κ * A = 0 := by ring
    rw [hzero_exp, Real.exp_zero]
  have hQ : Q ≤ y₀ * Real.exp (κ * A) := by
    calc
      Q = (Q * Real.exp ((-κ) * A)) * Real.exp (κ * A) := by
        rw [mul_assoc, hcancel, mul_one]
      _ ≤ y₀ * Real.exp (κ * A) :=
        mul_le_mul_of_nonneg_right hfactor (Real.exp_pos _).le
  have hA : A ≤ M := by
    have hmono : (∫ s in (0 : ℝ)..t, (y s) ^ 2) ≤
        ∫ s in (0 : ℝ)..T, (y s) ^ 2 :=
      intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
        (Filter.Eventually.of_forall (fun s => sq_nonneg (y s))) hi
    exact hmono.trans hbudget
  exact hQ.trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hA hκ)) hy₀)

/-- The exact-initial-value form, with no separate initial constant. -/
theorem CUBIC_ENERGY_OF_SQUARE_BUDGET_EXACT_INITIAL
    {y z d : ℝ → ℝ} {ν κ T M : ℝ}
    (hν : 0 < ν) (hκ : 0 ≤ κ) (hT : 0 ≤ T) (hM : 0 ≤ M)
    (hy : ContinuousOn y (Icc 0 T))
    (hz : ContinuousOn z (Icc 0 T))
    (hd : ContinuousOn d (Icc 0 T))
    (hy_nonneg : ∀ t ∈ Icc 0 T, 0 ≤ y t)
    (hderiv : ∀ t ∈ Ioo 0 T, HasDerivAt y (d t) t)
    (hcubic : ∀ t ∈ Ioo 0 T, d t + ν * (z t) ^ 2 ≤ κ * (y t) ^ 3)
    (hbudget : (∫ s in (0 : ℝ)..T, (y s) ^ 2) ≤ M) :
    ∀ t ∈ Icc 0 T,
      y t + ν * (∫ s in (0 : ℝ)..t, (z s) ^ 2) ≤ y 0 * Real.exp (κ * M) := by
  exact CUBIC_ENERGY_OF_SQUARE_BUDGET hν hκ hT hM hy hz hd hy_nonneg
    le_rfl hderiv hcubic hbudget

end SingularClosure
