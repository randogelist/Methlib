import SingularClosure.PhysicalParseval

/-!
NOETHER_CLOSURE / NC01
A named research premise, not an axiom declaration.
A normalized nonnegative charge Q is assumed to dominate the *actual physical*
Galerkin enstrophy on each finite horizon. Its initial value is uniformly
bounded over Galerkin cutoffs and over all trajectories of the same datum.
A Noether or dissipative-current construction of Q is NOT proved here.
-/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory
open scoped ENNReal NNReal

namespace SingularClosure
noncomputable section

def NOETHER_CHARGE_WINDOW (ν : ℝ) (a : Field) (T : ℝ) : Prop :=
  ∃ M : ℝ≥0,
    ∀ (N : ℕ), 1 ≤ N → ∀ (g : GalerkinSolution ν a N),
      ∃ Q : ℝ → ℝ≥0,
        (∀ t ∈ Icc (0 : ℝ) T,
          physicalEnstrophy (g.velocity t) ≤ (Q t : ℝ≥0∞)) ∧
        (∀ t ∈ Icc (0 : ℝ) T, Q t ≤ Q 0) ∧
        Q 0 ≤ M

/-- Exact universal normalized Noether-charge admission for finite horizons. -/
def NOETHER_CHARGE_ADMISSION : Prop :=
  ∀ (ν : ℝ), 0 < ν → ∀ (a : Field), SmoothSigmaZero a →
    ∀ (T : ℝ), 0 < T → NOETHER_CHARGE_WINDOW ν a T

end
end SingularClosure
