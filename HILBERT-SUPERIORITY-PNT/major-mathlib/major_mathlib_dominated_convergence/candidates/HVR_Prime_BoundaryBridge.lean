import HVR_Prime_InfiniteGram

noncomputable section

/-!
Conditional boundary bridge from the audited infinite prime Gram inequality.
The three normalized limits are hypotheses.  This file proves neither those
limits nor any actual zeta nonvanishing statement.
-/
namespace HVRPrimeBoundaryBridge

open Filter HVRPrimeInfinite

/-- The audited infinite inequality rules out the three residue-shaped
limits when the proposed first zero order is at least one and the second
zero order is nonnegative. Each convergence assertion is explicit. -/
theorem residue_limits_contradict_prime_gram
    (sigma delta : ℕ → ℝ) (t m q : ℝ)
    (hsigma : ∀ n, 1 < sigma n)
    (hdelta : ∀ n, 0 ≤ delta n)
    (hzero : Tendsto (fun n => delta n * primeMass (sigma n)) atTop (nhds 1))
    (hone : Tendsto (fun n => delta n * cosMoment (sigma n) t 1) atTop (nhds (-m)))
    (htwo : Tendsto (fun n => delta n * cosMoment (sigma n) t 2) atTop (nhds (-q)))
    (hm : 1 ≤ m) (hq : 0 ≤ q) : False := by
  have hnonneg : ∀ n,
      0 ≤ 3 * (delta n * primeMass (sigma n)) +
        4 * (delta n * cosMoment (sigma n) t 1) +
        delta n * cosMoment (sigma n) t 2 := by
    intro n
    calc
      0 ≤ delta n * (3 * primeMass (sigma n) +
          4 * cosMoment (sigma n) t 1 + cosMoment (sigma n) t 2) :=
        mul_nonneg (hdelta n) (infinite_prime_gram_nonnegative (sigma n) t (hsigma n))
      _ = 3 * (delta n * primeMass (sigma n)) +
          4 * (delta n * cosMoment (sigma n) t 1) +
          delta n * cosMoment (sigma n) t 2 := by ring
  have hlimit := ((hzero.const_mul (3 : ℝ)).add (hone.const_mul (4 : ℝ))).add htwo
  have hbound : 0 ≤ 3 * (1 : ℝ) + 4 * (-m) + (-q) :=
    ge_of_tendsto hlimit (Filter.Eventually.of_forall hnonneg)
  linarith

end HVRPrimeBoundaryBridge
