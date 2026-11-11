import SingularClosure.CubicBudget

/-!
# Cutoff-independent scalar consequences of the cubic budget

This module is an auxiliary to frozen endpoint 7.  Its conclusion is uniform
in the family index.  It does not construct the Galerkin enstrophy inequality,
identify a physical integral with a spectral sum, prove a time-derivative
estimate, or claim `AX6_UNIFORM_STRONG_BOUNDS`.

Every analytic hypothesis is displayed explicitly.  In particular the budget
constant occurs before the index quantifier.
-/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory
open scoped Interval

namespace SingularClosure

noncomputable section

/-- The scalar cubic estimate simultaneously bounds energy and accumulated
dissipation for an arbitrary family, with one constant independent of its index.
This is a scalar theorem, not the physical Galerkin endpoint 7. -/
theorem uniform_cubic_energy_of_square_budget
    {ι : Type*} {y z d : ι → ℝ → ℝ} {ν κ T M E₀ : ℝ}
    (hν : 0 < ν) (hκ : 0 ≤ κ) (hT : 0 ≤ T) (hM : 0 ≤ M)
    (hE₀ : 0 ≤ E₀)
    (hy : ∀ n, ContinuousOn (y n) (Icc 0 T))
    (hz : ∀ n, ContinuousOn (z n) (Icc 0 T))
    (hd : ∀ n, ContinuousOn (d n) (Icc 0 T))
    (hy_nonneg : ∀ n t, t ∈ Icc 0 T → 0 ≤ y n t)
    (h_initial : ∀ n, y n 0 ≤ E₀)
    (hderiv : ∀ n t, t ∈ Ioo 0 T → HasDerivAt (y n) (d n t) t)
    (hcubic : ∀ n t, t ∈ Ioo 0 T →
      d n t + ν * (z n t) ^ 2 ≤ κ * (y n t) ^ 3)
    (hbudget : ∀ n, (∫ s in (0 : ℝ)..T, (y n s) ^ 2) ≤ M) :
    ∃ B : ℝ, 0 ≤ B ∧ B = E₀ * Real.exp (κ * M) ∧
      ∀ n,
        (∀ t ∈ Icc 0 T,
          y n t + ν * (∫ s in (0 : ℝ)..t, (z n s) ^ 2) ≤ B) ∧
        (∀ t ∈ Icc 0 T, y n t ≤ B) ∧
        ν * (∫ s in (0 : ℝ)..T, (z n s) ^ 2) ≤ B := by
  let B := E₀ * Real.exp (κ * M)
  refine ⟨B, mul_nonneg hE₀ (Real.exp_pos _).le, rfl, ?_⟩
  intro n
  have h := CUBIC_ENERGY_OF_SQUARE_BUDGET hν hκ hT hM
    (hy n) (hz n) (hd n) (hy_nonneg n) (h_initial n)
    (hderiv n) (hcubic n) (hbudget n)
  refine ⟨h, ?_, ?_⟩
  · intro t ht
    have hI : 0 ≤ ∫ s in (0 : ℝ)..t, (z n s) ^ 2 :=
      intervalIntegral.integral_nonneg_of_forall ht.1 (fun s => sq_nonneg _)
    exact (le_add_of_nonneg_right (mul_nonneg hν.le hI)).trans (h t ht)
  · have hend : T ∈ Icc (0 : ℝ) T := ⟨hT, le_rfl⟩
    exact (le_add_of_nonneg_left (hy_nonneg n T hend)).trans (h T hend)

end

end SingularClosure
