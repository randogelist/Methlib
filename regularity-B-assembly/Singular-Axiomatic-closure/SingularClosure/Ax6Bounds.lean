import SingularClosure.PhysicalEnstrophy

/-!
# Actual physical square budget implied by AX6

This implication uses the concrete six-channel derivative reconstruction.
The same finite constant controls all cutoffs and all actual trajectories.
No Galerkin existence theorem or enstrophy differential inequality is assumed.
Those remain separate steps toward the frozen uniform strong-bounds endpoint.
-/

set_option autoImplicit false

open Set MeasureTheory
open scoped ENNReal NNReal

namespace SingularClosure

noncomputable section

/-- The frozen admission controls the actual physical square-enstrophy budget,
uniformly in the cutoff, with the explicit reconstruction factor 36. -/
theorem ax6_physical_square_budget (hAX6 : AX6Statement)
    (ν : ℝ) (hν : 0 < ν) (a : Field) (ha : SmoothSigmaZero a)
    (T : ℝ) (hT : 0 < T) :
    ∃ M : ℝ≥0, ∀ N : ℕ, 1 ≤ N → ∀ g : GalerkinSolution ν a N,
      (∫⁻ t in Icc (0 : ℝ) T, (physicalEnstrophy (g.velocity t)) ^ 2) ≤
        (M : ℝ≥0∞) := by
  obtain ⟨M, hM⟩ := hAX6 ν hν a ha T hT
  refine ⟨36 * M, ?_⟩
  intro N hN g
  have h := (PHYSICAL_SQUARE_BUDGET_LE_AX6_BUDGET N g.coeff T).trans
    (mul_le_mul_left' (hM N hN g) (36 : ℝ≥0∞))
  simpa only [GalerkinSolution.velocity, ENNReal.coe_mul, ENNReal.coe_ofNat] using h

end

end SingularClosure
