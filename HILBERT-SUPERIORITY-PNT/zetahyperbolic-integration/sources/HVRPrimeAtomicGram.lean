import HVR_Prime_Gram

/-!
Finite prime atomic Gram identities, in the style of the bilinear integral
identity in Zetahyperbolic's MomentPositivity and Section3OrthogonalKernel.

This file constructs the actual HVR prime-cutoff object using
`HVRPrimeGram.primesUpTo` and `HVRPrimeGram.primeWeight`.  It establishes
a finite identity, nonnegativity, and strict positivity conditional on a
prime-node witness. It does not prove unconditional strict
positive-definiteness, an infinite prime-moment limit, a zeta identity, or
the PNT.  The proof is an independent
finite-sum adaptation; no old binary object or Lean 4.33 source audit is
represented as a Lean 4.34 audit.
-/

noncomputable section
open scoped BigOperators

namespace HVRPrimeAtomicGram

/-- Powers of the logarithmic prime spectral coordinate. -/
def feature (h : ℕ) (i : Fin h) (p : ℕ) : ℝ :=
  (Real.log (p : ℝ)) ^ i.val

/-- Finite actual-prime spectral Gram entry. -/
def gramEntry (N : ℕ) (sigma : ℝ) (h : ℕ) (i j : Fin h) : ℝ :=
  ∑ p ∈ HVRPrimeGram.primesUpTo N,
    HVRPrimeGram.primeWeight sigma p * feature h i p * feature h j p

/-- Evaluate the polynomial represented by `c` at the prime log-node. -/
def evalFeature {h : ℕ} (c : Fin h → ℝ) (p : ℕ) : ℝ :=
  ∑ i : Fin h, c i * feature h i p

/-- The scalar quadratic expression of the finite Gram entries. -/
def quadratic {h : ℕ} (N : ℕ) (sigma : ℝ) (c : Fin h → ℝ) : ℝ :=
  ∑ i : Fin h, ∑ j : Fin h, c i * gramEntry N sigma h i j * c j

/-- Zetahyperbolic-style Gram identity for the actual finite HVR prime
spectral nodes and weights. No convergence premise is needed for a cutoff. -/
theorem quadratic_eq_prime_sum (N : ℕ) (sigma : ℝ) (h : ℕ)
    (c : Fin h → ℝ) :
    quadratic N sigma c =
      ∑ p ∈ HVRPrimeGram.primesUpTo N,
        HVRPrimeGram.primeWeight sigma p * (evalFeature c p) ^ 2 := by
  classical
  unfold quadratic gramEntry
  calc
    (∑ i : Fin h, ∑ j : Fin h,
      c i * (∑ p ∈ HVRPrimeGram.primesUpTo N,
        HVRPrimeGram.primeWeight sigma p * feature h i p * feature h j p) * c j)
      = ∑ i : Fin h, ∑ j : Fin h,
          ∑ p ∈ HVRPrimeGram.primesUpTo N,
            c i * (HVRPrimeGram.primeWeight sigma p * feature h i p * feature h j p) * c j := by
              simp only [Finset.mul_sum, Finset.sum_mul]
    _ = ∑ i : Fin h, ∑ p ∈ HVRPrimeGram.primesUpTo N,
          ∑ j : Fin h,
            c i * (HVRPrimeGram.primeWeight sigma p * feature h i p * feature h j p) * c j := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [Finset.sum_comm]
    _ = ∑ p ∈ HVRPrimeGram.primesUpTo N, ∑ i : Fin h, ∑ j : Fin h,
          c i * (HVRPrimeGram.primeWeight sigma p * feature h i p * feature h j p) * c j := by
              rw [Finset.sum_comm]
    _ = ∑ p ∈ HVRPrimeGram.primesUpTo N,
          HVRPrimeGram.primeWeight sigma p * (evalFeature c p) ^ 2 := by
              apply Finset.sum_congr rfl
              intro p hp
              unfold evalFeature
              simp only [pow_two, Finset.mul_sum, Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro i hi
              apply Finset.sum_congr rfl
              intro j hj
              ring

/-- Every finite HVR prime-cutoff Gram quadratic form is nonnegative. -/
theorem quadratic_nonnegative (N : ℕ) (sigma : ℝ) (h : ℕ)
    (c : Fin h → ℝ) : 0 ≤ quadratic N sigma c := by
  rw [quadratic_eq_prime_sum]
  apply Finset.sum_nonneg
  intro p hp
  exact mul_nonneg
    (HVRPrimeGram.primeWeight_nonneg sigma (Finset.mem_filter.mp hp).2)
    (sq_nonneg (evalFeature c p))

/-- Strict positivity when the coefficient polynomial is nonzero at a
specific prime in the cutoff.  This explicit witness is not a proof that
every nonzero polynomial has a nonzero value at a prime in a given cutoff. -/
theorem quadratic_pos_of_prime_witness (N : ℕ) (sigma : ℝ) (h : ℕ)
    (c : Fin h → ℝ) {p : ℕ} (hp : p ∈ HVRPrimeGram.primesUpTo N)
    (hnode : evalFeature c p ≠ 0) : 0 < quadratic N sigma c := by
  rw [quadratic_eq_prime_sum]
  have hprime : Nat.Prime p := (Finset.mem_filter.mp hp).2
  have hp_gt : (1 : ℝ) < (p : ℝ) := by
    have hnat : 1 < p := by have := hprime.two_le; omega
    exact_mod_cast hnat
  have hw : 0 < HVRPrimeGram.primeWeight sigma p := by
    unfold HVRPrimeGram.primeWeight
    exact mul_pos (Real.log_pos hp_gt) (Real.exp_pos _)
  have hterm : 0 < HVRPrimeGram.primeWeight sigma p * (evalFeature c p) ^ 2 :=
    mul_pos hw (sq_pos_of_ne_zero hnode)
  have hle : HVRPrimeGram.primeWeight sigma p * (evalFeature c p) ^ 2 ≤
      ∑ q ∈ HVRPrimeGram.primesUpTo N,
        HVRPrimeGram.primeWeight sigma q * (evalFeature c q) ^ 2 := by
    apply Finset.single_le_sum
    · intro q hq
      exact mul_nonneg
        (HVRPrimeGram.primeWeight_nonneg sigma (Finset.mem_filter.mp hq).2)
        (sq_nonneg (evalFeature c q))
    · exact hp
  exact lt_of_lt_of_le hterm hle

/-- The upper-left Gram entry is the existing HVR finite prime mass. -/
theorem gramEntry_zero_zero (N : ℕ) (sigma : ℝ) (h : ℕ) (hh : 0 < h) :
    gramEntry N sigma h ⟨0, hh⟩ ⟨0, hh⟩ = HVRPrimeGram.primeMass N sigma := by
  simp [gramEntry, feature, HVRPrimeGram.primeMass]

end HVRPrimeAtomicGram
