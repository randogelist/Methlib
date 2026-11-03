import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

/-!
Candidate reconstruction of the von Mangoldt value at an actual prime.
The proof unfolds the arithmetic function's defining prime-power case and
uses the least-prime-factor identity. It does not explicitly call
`ArithmeticFunction.vonMangoldt_apply_prime`.

This source has not been compiled or axiom-audited. The transitive dependency
closure must be examined before asserting independence from the original lemma.
-/

namespace HVRNativeMangoldtPrime

/-- The actual von Mangoldt value at a prime is its natural logarithm. -/
theorem vonMangoldt_apply_prime_native {p : ℕ} (hp : p.Prime) :
    ArithmeticFunction.vonMangoldt p = Real.log (p : ℝ) := by
  change (if IsPrimePow p then Real.log (Nat.minFac p) else 0) = Real.log (p : ℝ)
  have hpow : IsPrimePow p := hp.prime.isPrimePow
  rw [if_pos hpow, Nat.Prime.minFac_eq hp]

end HVRNativeMangoldtPrime
