/-! Optional actual OAI/30k30 external proof adapter.
    Requires Lean 4.34.1, matching Mathlib d13f23b7 and genuinely compiled upstream OLEANs.
    NOT compiled by the rc1 core CI; it must never be substituted by an axiom. -/
import ERDOS_687_CRT_BKQR
import JacobsthalTo687

namespace Erdos687AttemptC

theorem actual_external_partial : ExternalPartialBound := by
  simpa only [ExternalPartialBound, Covers, Erdos687.Covers] using
    erdos_687_little_o

theorem ROOT_EXTERNAL_AND_BKQR :
    ExternalPartialBound ∧
      (∀ x y : ℕ,
        certificateMass (primorial x) y (spike y) < 1 ↔
          EveryShiftSurvives (primorial x) y) :=
  external_partial_plus_certificate actual_external_partial

#print axioms Erdos687AttemptC.actual_external_partial
#print axioms Erdos687AttemptC.ROOT_EXTERNAL_AND_BKQR

end Erdos687AttemptC
