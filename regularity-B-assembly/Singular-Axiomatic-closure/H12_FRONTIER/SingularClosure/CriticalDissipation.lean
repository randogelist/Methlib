import SingularClosure.CriticalInvariant

/-! Critical L²-in-time dissipation from the proved scalar invariant. -/

set_option autoImplicit false
set_option Elab.async true

noncomputable section

open Set MeasureTheory
open scoped Interval

namespace SingularClosure

theorem CRITICAL_DISSIPATION_BUDGET
    {A B d : ℝ → ℝ} {ν C a₀ T : ℝ}
    (hT : 0 ≤ T) (hC : 0 ≤ C) (ha₀ : 0 ≤ a₀)
    (hsmall : C * a₀ < ν)
    (hA : ContinuousOn A (Icc 0 T))
    (hBc : ContinuousOn B (Icc 0 T))
    (hAnonneg : ∀ t ∈ Icc 0 T, 0 ≤ A t)
    (hB : ∀ t ∈ Icc 0 T, 0 ≤ B t)
    (hinit : A 0 ≤ a₀ ^ 2)
    (hderiv : ∀ t ∈ Ico 0 T, HasDerivWithinAt A (d t) (Ici 0) t)
    (hcritical : ∀ t ∈ Ico 0 T,
      d t + 2 * (ν - C * Real.sqrt (A t)) * B t ≤ 0) :
    ∀ t ∈ Icc 0 T,
      A t + 2 * (ν - C * a₀) * (∫ s in (0 : ℝ)..t, B s) ≤ a₀ ^ 2 := by
  have hδ : 0 ≤ ν - C * a₀ := (sub_pos.mpr hsmall).le
  have hb := critical_uniform_dissipation_inequality hT hC ha₀ hsmall hA
    (fun t ht => hB t ⟨ht.1, ht.2.le⟩) hinit hderiv hcritical
  have hd : ∀ t ∈ Ioo 0 T, HasDerivAt A (d t) t := by
    intro t ht
    exact (hderiv t ⟨ht.1.le, ht.2⟩).hasDerivAt (Ici_mem_nhds ht.1)
  have hi : ∀ t ∈ Ioo 0 T,
      d t + (2 * (ν - C * a₀)) * (Real.sqrt (B t)) ^ 2 ≤ (0 : ℝ) * A t := by
    intro t ht
    rw [Real.sq_sqrt (hB t ⟨ht.1.le, ht.2.le⟩), zero_mul]
    exact hb t ⟨ht.1.le, ht.2⟩
  have h := LINEAR_ENERGY_OF_COEFFICIENT_BUDGET
    (y := A) (z := fun t => Real.sqrt (B t)) (d := d)
    (a := fun _ => (0 : ℝ)) (ν := 2 * (ν - C * a₀)) (M := 0) (y₀ := a₀ ^ 2)
    (mul_nonneg (by norm_num) hδ) hT hA
    (Real.continuous_sqrt.comp_continuousOn hBc) continuousOn_const
    hAnonneg (fun _ _ => le_rfl) hinit hd hi (by simp)
  intro t ht
  have heq : (∫ s in (0 : ℝ)..t, (Real.sqrt (B s)) ^ 2) =
      ∫ s in (0 : ℝ)..t, B s := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le ht.1] at hs
    exact Real.sq_sqrt (hB s ⟨hs.1, hs.2.trans ht.2⟩)
  have htbound := h t ht
  simpa only [heq, Real.exp_zero, mul_one] using htbound

end SingularClosure
