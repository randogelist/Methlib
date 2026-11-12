import SingularityDisprovement.DyadicArithmetic

open SingularityDisprovement
open scoped BigOperators

example :
    (∀ j : ℕ, 1 ≤ j →
      (∑ n ∈ Finset.Ico ((2 : ℕ) ^ j) (2 ^ (j + 1)), dyadicAmplitude n) = 1 / (j : ℝ)) ∧
    (∀ j : ℕ, 1 ≤ j →
      (∑ n ∈ Finset.Ico ((2 : ℕ) ^ j) (2 ^ (j + 1)), dyadicAmplitude n ^ 2) =
        1 / ((j : ℝ) ^ 2 * (2 : ℝ) ^ j)) ∧
    (∀ j : ℕ, 1 ≤ j →
      (∑ n ∈ Finset.Ico ((2 : ℕ) ^ j) (2 ^ (j + 1)), (n : ℝ) * dyadicAmplitude n ^ 2) =
        (3 - (2 : ℝ) ^ (- (j : ℤ))) / (2 * (j : ℝ) ^ 2)) ∧
    (0 < dyadicR ∧ dyadicR < 1) ∧ (0 < dyadicS ∧ dyadicS < 6) :=
  DYADIC_BLOCK_IDENTITIES

#eval IO.println "EXACT_TYPE_PASS:SingularityDisprovement.DYADIC_BLOCK_IDENTITIES"
#check @SingularityDisprovement.DYADIC_BLOCK_IDENTITIES
#print axioms SingularityDisprovement.DYADIC_BLOCK_IDENTITIES
