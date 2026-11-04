import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

/-!
Candidate reconstruction of the actual von Mangoldt value at a positive
natural exponent. It unfolds the prime-power definition and reduces to the
prime-power and minimum-factor identities for positive exponents. This source
does not explicitly call `ArithmeticFunction.vonMangoldt_apply_pow`.

Status: source candidate only. It has not been compiled or axiom-audited.
Inspect recursive declaration dependencies before claiming independence.
-/

namespace HVRNativeMangoldtPow

open Nat

/-- Positive powers preserve the actual von Mangoldt value. -/
theorem vonMangoldt_apply_pow_native {n k : ℕ} (hk : k ≠ 0) :
    ArithmeticFunction.vonMangoldt (n ^ k) = ArithmeticFunction.vonMangoldt n := by
  change (if IsPrimePow (n ^ k) then Real.log (Nat.minFac (n ^ k)) else 0) =
    (if IsPrimePow n then Real.log (Nat.minFac n) else 0)
  simp only [isPrimePow_pow_iff hk, pow_minFac hk]

end HVRNativeMangoldtPow
