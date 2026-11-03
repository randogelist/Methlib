import HVR_Prime_Summability
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Order

open scoped BigOperators

noncomputable section

/-!
Infinite prime Gram positivity. The half-plane hypothesis sigma > 1
ensures that each sum appearing below is a genuine convergent series.
This module establishes no continuation, zero-free boundary, or PNT.
-/
namespace HVRPrimeInfinite

open HVRPrimeSummability

def primeMass (sigma : ℝ) : ℝ :=
  ∑' n : ℕ, primeWeightSeries sigma n

def cosTerm (sigma t frequency : ℝ) (n : ℕ) : ℝ :=
  primeWeightSeries sigma n * Real.cos (frequency * (t * Real.log (n : ℝ)))

def cosMoment (sigma t frequency : ℝ) : ℝ :=
  ∑' n : ℕ, cosTerm sigma t frequency n

/-- The cosine factor has modulus at most one. -/
theorem cosMoment_summable (sigma t frequency : ℝ) (hsigma : 1 < sigma) :
    Summable (cosTerm sigma t frequency) := by
  have hw : Summable (primeWeightSeries sigma) :=
    primeWeightSeries_summable sigma hsigma
  apply Summable.of_norm_bounded hw
  intro n
  rw [cosTerm, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (primeWeightSeries_nonneg sigma n)]
  calc
    primeWeightSeries sigma n *
        |Real.cos (frequency * (t * Real.log (n : ℝ)))| ≤
        primeWeightSeries sigma n * 1 :=
      mul_le_mul_of_nonneg_left
        (Real.abs_cos_le_one (frequency * (t * Real.log (n : ℝ))))
        (primeWeightSeries_nonneg sigma n)
    _ = primeWeightSeries sigma n := mul_one _

/-- The summand has the certified nonnegative kernel. -/
theorem gramTerm_nonneg (sigma t : ℝ) (n : ℕ) :
    0 ≤ 3 * primeWeightSeries sigma n + 4 * cosTerm sigma t 1 n +
      cosTerm sigma t 2 n := by
  simp only [cosTerm, one_mul]
  have hk := HVRPrimeGram.kernel_identity (t * Real.log (n : ℝ))
  have hweight := primeWeightSeries_nonneg sigma n
  have hsq : 0 ≤ 2 * primeWeightSeries sigma n *
      (1 + Real.cos (t * Real.log (n : ℝ))) ^ 2 := by
    exact mul_nonneg (mul_nonneg (by norm_num) hweight) (sq_nonneg _)
  have hmul := congrArg (fun x : ℝ => primeWeightSeries sigma n * x) hk
  nlinarith [hmul]

/-- For sigma > 1, the actual three prime sums converge and obey the
nonnegative Gram inequality. No limiting or zeta hypothesis is assumed. -/
theorem infinite_prime_gram_nonnegative (sigma t : ℝ) (hsigma : 1 < sigma) :
    0 ≤ 3 * primeMass sigma + 4 * cosMoment sigma t 1 +
      cosMoment sigma t 2 := by
  have hw : Summable (primeWeightSeries sigma) :=
    primeWeightSeries_summable sigma hsigma
  have hc1 : Summable (cosTerm sigma t 1) := cosMoment_summable sigma t 1 hsigma
  have hc2 : Summable (cosTerm sigma t 2) := cosMoment_summable sigma t 2 hsigma
  have hsum := ((hw.hasSum.mul_left (3 : ℝ)).add
    (hc1.hasSum.mul_left (4 : ℝ))).add hc2.hasSum
  change 0 ≤ 3 * (∑' n : ℕ, primeWeightSeries sigma n) +
    4 * (∑' n : ℕ, cosTerm sigma t 1 n) +
    (∑' n : ℕ, cosTerm sigma t 2 n)
  exact HasSum.nonneg (gramTerm_nonneg sigma t) hsum

end HVRPrimeInfinite

#print axioms HVRPrimeInfinite.cosMoment_summable
#print axioms HVRPrimeInfinite.gramTerm_nonneg
#print axioms HVRPrimeInfinite.infinite_prime_gram_nonnegative
