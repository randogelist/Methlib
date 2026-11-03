import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

open scoped BigOperators

noncomputable section

/-!
Finite prime-only positivity for the HVR prime number theorem programme.

The root result concerns a *finite* prime sum. It does not assert the
infinite Gram identity, zero-freeness, the Tauberian bridge, or PNT.
No pre-existing PNT theorem is invoked in these proofs.
-/

namespace HVRPrimeGram

def primesUpTo (N : ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).filter Nat.Prime

def primeWeight (sigma : ℝ) (p : ℕ) : ℝ :=
  Real.log (p : ℝ) * Real.exp (-sigma * Real.log (p : ℝ))

def primeMass (N : ℕ) (sigma : ℝ) : ℝ :=
  ∑ p ∈ primesUpTo N, primeWeight sigma p

def primeCosMoment (N : ℕ) (sigma t frequency : ℝ) : ℝ :=
  ∑ p ∈ primesUpTo N,
    primeWeight sigma p * Real.cos (frequency * (t * Real.log (p : ℝ)))

theorem kernel_identity (u : ℝ) :
    3 + 4 * Real.cos u + Real.cos (2 * u) =
      2 * (1 + Real.cos u) ^ 2 := by
  rw [Real.cos_two_mul]
  ring

theorem primeWeight_nonneg (sigma : ℝ) {p : ℕ} (hp : Nat.Prime p) :
    0 ≤ primeWeight sigma p := by
  have hp_one : (1 : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast (show 1 ≤ p from Nat.le_trans (by decide) hp.two_le)
  exact mul_nonneg (Real.log_nonneg hp_one) (le_of_lt (Real.exp_pos _))

theorem finite_prime_gram_identity (N : ℕ) (sigma t : ℝ) :
    3 * primeMass N sigma + 4 * primeCosMoment N sigma t 1 +
        primeCosMoment N sigma t 2 =
      2 * ∑ p ∈ primesUpTo N,
        primeWeight sigma p * (1 + Real.cos (t * Real.log (p : ℝ))) ^ 2 := by
  simp only [primeMass, primeCosMoment, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  simp only [one_mul]
  calc
    _ = primeWeight sigma p *
        (3 + 4 * Real.cos (t * Real.log (p : ℝ)) +
          Real.cos (2 * (t * Real.log (p : ℝ)))) := by ring
    _ = primeWeight sigma p *
        (2 * (1 + Real.cos (t * Real.log (p : ℝ))) ^ 2) := by
          rw [kernel_identity]
    _ = _ := by ring

theorem finite_prime_gram_nonnegative (N : ℕ) (sigma t : ℝ) :
    0 ≤ 3 * primeMass N sigma + 4 * primeCosMoment N sigma t 1 +
      primeCosMoment N sigma t 2 := by
  rw [finite_prime_gram_identity]
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg
  intro p hp
  exact mul_nonneg (primeWeight_nonneg sigma (Finset.mem_filter.mp hp).2)
    (sq_nonneg _)

/-- The normalized boundary limit is an explicit hypothesis, not an
assertion that the analytic zeta boundary has already been constructed. -/
theorem normalized_limit_excludes_zero_order
    (a : ℕ → ℝ) (m q : ℝ)
    (ha : ∀ n, 0 ≤ a n)
    (hlim : Filter.Tendsto a Filter.atTop (nhds (3 - 4 * m - q)))
    (hm : 1 ≤ m) (hq : 0 ≤ q) : False := by
  have hnonneg : 0 ≤ 3 - 4 * m - q :=
    ge_of_tendsto hlim (Filter.Eventually.of_forall ha)
  linarith

/-- A conditional sequential edge from the actual finite prime sums.
The limit and its identification with zero orders remain premises. -/
theorem finite_prime_limit_excludes_zero_order
    (N : ℕ → ℕ) (sigma t delta : ℕ → ℝ) (m q : ℝ)
    (hdelta : ∀ n, 0 ≤ delta n)
    (hlim : Filter.Tendsto
      (fun n => delta n *
        (3 * primeMass (N n) (sigma n) +
         4 * primeCosMoment (N n) (sigma n) (t n) 1 +
         primeCosMoment (N n) (sigma n) (t n) 2))
      Filter.atTop (nhds (3 - 4 * m - q)))
    (hm : 1 ≤ m) (hq : 0 ≤ q) : False := by
  apply normalized_limit_excludes_zero_order _ m q _ hlim hm hq
  intro n
  exact mul_nonneg (hdelta n) (finite_prime_gram_nonnegative (N n) (sigma n) (t n))

end HVRPrimeGram

#print axioms HVRPrimeGram.kernel_identity
#print axioms HVRPrimeGram.primeWeight_nonneg
#print axioms HVRPrimeGram.finite_prime_gram_identity
#print axioms HVRPrimeGram.finite_prime_gram_nonnegative
#print axioms HVRPrimeGram.normalized_limit_excludes_zero_order
#print axioms HVRPrimeGram.finite_prime_limit_excludes_zero_order
