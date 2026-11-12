import SingularClosure.LinearBudget

/-! Time translation and averaging for positive-time parabolic estimates. -/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory
open scoped Interval

namespace SingularClosure
noncomputable section

theorem critical_exists_energy_le_average {y : ℝ → ℝ} {a b B : ℝ}
    (hab : a < b) (hy : ContinuousOn y (Icc a b))
    (hbudget : (∫ s in a..b, y s) ≤ B) :
    ∃ r ∈ Icc a b, y r ≤ B / (b - a) := by
  obtain ⟨r, hr, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hab.le) hy
  refine ⟨r, hr, (le_div_iff₀ (sub_pos.mpr hab)).mpr ?_⟩
  have h : (∫ _s in a..b, y r) ≤ ∫ s in a..b, y s :=
    intervalIntegral.integral_mono_on hab.le intervalIntegrable_const
      (hy.intervalIntegrable_of_Icc hab.le) (fun s hs => hmin hs)
  have h' : y r * (b - a) ≤ ∫ s in a..b, y s := by
    simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_comm] using h
  exact h'.trans hbudget

theorem critical_shifted_linear_energy_budget
    {y z d a : ℝ → ℝ} {ν r T M y₀ : ℝ}
    (hν : 0 ≤ ν) (hrT : r ≤ T)
    (hy : ContinuousOn y (Icc r T))
    (hz : ContinuousOn z (Icc r T))
    (ha : ContinuousOn a (Icc r T))
    (hy_nonneg : ∀ t ∈ Icc r T, 0 ≤ y t)
    (ha_nonneg : ∀ t ∈ Icc r T, 0 ≤ a t)
    (h_initial : y r ≤ y₀)
    (hderiv : ∀ t ∈ Ioo r T, HasDerivAt y (d t) t)
    (hlinear : ∀ t ∈ Ioo r T, d t + ν * (z t) ^ 2 ≤ a t * y t)
    (hbudget : (∫ s in r..T, a s) ≤ M) :
    ∀ t ∈ Icc r T,
      y t + ν * (∫ s in r..t, (z s) ^ 2) ≤ y₀ * Real.exp M := by
  have hmap : MapsTo (fun s : ℝ => s + r) (Icc 0 (T - r)) (Icc r T) := by
    intro s hs
    constructor <;> linarith [hs.1, hs.2]
  have hy' : ContinuousOn (fun s => y (s + r)) (Icc 0 (T - r)) :=
    hy.comp (continuous_add_const r).continuousOn hmap
  have hz' : ContinuousOn (fun s => z (s + r)) (Icc 0 (T - r)) :=
    hz.comp (continuous_add_const r).continuousOn hmap
  have ha' : ContinuousOn (fun s => a (s + r)) (Icc 0 (T - r)) :=
    ha.comp (continuous_add_const r).continuousOn hmap
  have hd' (s : ℝ) (hs : s ∈ Ioo 0 (T - r)) :
      HasDerivAt (fun q => y (q + r)) (d (s + r)) s := by
    have hsr : s + r ∈ Ioo r T := by
      constructor <;> linarith [hs.1, hs.2]
    simpa only [Function.comp_def, mul_one] using!
      (hderiv (s + r) hsr).comp s ((hasDerivAt_id s).add_const r)
  have hl' (s : ℝ) (hs : s ∈ Ioo 0 (T - r)) :
      d (s + r) + ν * z (s + r) ^ 2 ≤ a (s + r) * y (s + r) := by
    apply hlinear
    constructor <;> linarith [hs.1, hs.2]
  have hb' : (∫ s in (0 : ℝ)..(T - r), a (s + r)) ≤ M := by
    simpa only [intervalIntegral.integral_comp_add_right, zero_add, sub_add_cancel] using hbudget
  have h := LINEAR_ENERGY_OF_COEFFICIENT_BUDGET hν (sub_nonneg.mpr hrT)
    hy' hz' ha'
    (fun s hs => hy_nonneg (s + r) (hmap hs))
    (fun s hs => ha_nonneg (s + r) (hmap hs))
    (by simpa only [zero_add] using h_initial) hd' hl' hb'
  intro t ht
  have ht' : t - r ∈ Icc 0 (T - r) := by
    constructor <;> linarith [ht.1, ht.2]
  have hv := h (t - r) ht'
  have hshift : (∫ s in (0 : ℝ)..(t - r), z (s + r) ^ 2) =
      ∫ s in r..t, z s ^ 2 := by
    simpa only [zero_add, sub_add_cancel] using
      (intervalIntegral.integral_comp_add_right (fun s => z s ^ 2) r
        (a := (0 : ℝ)) (b := t - r))
  simpa only [sub_add_cancel, hshift] using hv

end
end SingularClosure
