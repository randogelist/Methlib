import HVR_PrimeMomentJacobi

/-!
Finite prime mass decay. The determinant/Laplace perspective is motivated by
snditeration's Section3 LaplaceJacobiIdentity. This independent finite-sum
specialization uses the HVR prime weights and actual primes up to N.
No infinite-prime, zeta, or PNT endpoint is asserted. Candidate only: external
compilation and theorem-level axiom audit are required.
-/

noncomputable section
open scoped BigOperators

namespace HVRPrimeMomentDecay

open HVRPrimeGram HVRPrimeMomentJacobi

/-- The first logarithmic moment is at least log(2) times the prime mass. -/
theorem log_two_mul_mass_le_first_moment (N : ℕ) (σ : ℝ) :
    Real.log 2 * primeMass N σ ≤ moment N σ 1 := by
  have hterm : ∀ p ∈ primesUpTo N,
      Real.log 2 * primeWeight σ p ≤
        primeWeight σ p * Real.log (p : ℝ) := by
    intro p hp
    have hprime : Nat.Prime p := (Finset.mem_filter.mp hp).2
    have htwo : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hprime.two_le
    have hlog : Real.log 2 ≤ Real.log (p : ℝ) :=
      Real.log_le_log (by norm_num) htwo
    have hw : 0 ≤ primeWeight σ p := primeWeight_nonneg σ hprime
    nlinarith [mul_le_mul_of_nonneg_left hlog hw]
  have hs := Finset.sum_le_sum hterm
  simpa only [moment, primeMass, pow_one, Finset.mul_sum] using hs

/-- The logarithmic derivative of positive finite prime mass is at most
minus log(2). This is an actual cutoff identity and bound, with no prime-node
witness beyond the cutoff containing 2. -/
theorem log_mass_derivative_le_neg_log_two (N : ℕ) (σ : ℝ) (hN : 2 ≤ N) :
    HasDerivAt (fun z : ℝ => Real.log (primeMass N z))
      (-(moment N σ 1) / primeMass N σ) σ ∧
      -(moment N σ 1) / primeMass N σ ≤ -Real.log 2 := by
  refine ⟨log_primeMass_hasDerivAt N σ hN, ?_⟩
  have hm : 0 < primeMass N σ := primeMass_pos N σ hN
  apply (div_le_iff₀ hm).2
  have h := log_two_mul_mass_le_first_moment N σ
  nlinarith

end HVRPrimeMomentDecay
