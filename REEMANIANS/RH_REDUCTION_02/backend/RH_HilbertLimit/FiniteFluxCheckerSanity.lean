import RH_HilbertLimit.FiniteFluxActualBridge

/-!
# Regression: algebraic acceptance is not actual-Hilbert admission

The v0.2.36 Bool checker tests only finite syntax and tautological algebraic
weighted-sum identities.  Consequently it admits an all-zero example.  This
regression is intentional and documents why the actual interpretation bridge
cannot be silently omitted from the forward RH theorem.

This example is NOT an RH witness.  A final mathematical checker must restrict
certificate premises to theorems actually valid of the actual xi/Bernstein
quantities and bind the checked goal to the genuine cancellation slack.
-/

set_option autoImplicit false
noncomputable section

namespace RH_HilbertLimit

/-- Exact algebraic zero identity: 0 equals the empty weighted sum. -/
def algebraicOnlyZeroCertificate : LinearFluxCertificate :=
  { arity := 1
    maxNodes := 1
    terms := []
    goal := FluxProofExpr.const 0 }

/-- A syntactic rule with zero slack, used only by the regression witness. -/
def algebraicOnlyZeroRule (r : FluxRegion) : FluxRule :=
  { region := r
    slack := FluxExpr.const 0
    multiplier := 0 }

/-- The deliberately trivial raw finite-data object, not a sound RH witness. -/
def algebraicOnlyZeroRaw : FiniteFluxWitness :=
  { coefficient := 0
    generator := FluxExpr.const 0
    stepCert :=
      { maxNodes := 1
        rules := [algebraicOnlyZeroRule FluxRegion.left,
          algebraicOnlyZeroRule FluxRegion.interior,
          algebraicOnlyZeroRule FluxRegion.right,
          algebraicOnlyZeroRule FluxRegion.boundary] } }

/-- All four regions admit the same tautological zero certificate. -/
def algebraicOnlyZeroWitness : FiniteFluxCheckedWitness :=
  { raw := algebraicOnlyZeroRaw
    regions :=
      { left := algebraicOnlyZeroCertificate
        interior := algebraicOnlyZeroCertificate
        right := algebraicOnlyZeroCertificate
        boundary := algebraicOnlyZeroCertificate } }

/-- Regression theorem: the existing algebraic Bool check accepts the dummy.
This is an algebraic syntax fact only; NO actual xi/RH soundness is claimed. -/
theorem algebraicOnlyZeroWitness_check :
    algebraicOnlyZeroWitness.check = true := by
  decide

end RH_HilbertLimit
