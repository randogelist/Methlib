import HVR_Correction_UniformBound
import Mathlib.NumberTheory.EulerProduct.Basic

noncomputable section

/-!
Reindex the complex correction by the subtype of prime natural numbers.
This is an identity for the actual correction term and does not assume or
establish an equality with the higher-coefficient L-series or PNT. This
candidate still requires an external Lean build and axiom audit.
-/
namespace HVRCorrectionPrimeSubtype

open HVRPowerCorrectionHolomorphic

/-- The correction term vanishes outside the primes. -/
theorem complexCorrectionTerm_support (z : ℂ) :
    Function.support (fun n : ℕ => complexCorrectionTerm n z) ⊆
      {n : ℕ | Nat.Prime n} := by
  intro n hn
  change complexCorrectionTerm n z ≠ 0 at hn
  change Nat.Prime n
  by_contra hp
  apply hn
  simp [complexCorrectionTerm, hp]

/-- The full natural-number sum equals the sum over prime indices. -/
theorem complexCorrection_eq_prime_tsum (z : ℂ) :
    complexCorrection z = ∑' p : Nat.Primes, complexCorrectionTerm (p : ℕ) z := by
  unfold complexCorrection
  exact (tsum_subtype_eq_of_support_subset (complexCorrectionTerm_support z)).symm

/-- At a prime index, the term is the explicit resummed geometric expression. -/
theorem complexCorrectionTerm_at_prime (p : Nat.Primes) (z : ℂ) :
    complexCorrectionTerm (p : ℕ) z =
      (Real.log ((p : ℕ) : ℝ) : ℂ) * (complexRatio (p : ℕ) z) ^ 2 /
        (1 - complexRatio (p : ℕ) z) := by
  simp only [complexCorrectionTerm, if_pos p.property]

end HVRCorrectionPrimeSubtype
