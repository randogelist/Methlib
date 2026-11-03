import Mathlib.NumberTheory.Chebyshev
import Mathlib.Tactic

/-!
A candidate proof of nonnegativity for the actual Chebyshev theta function.
The argument expands theta as a finite sum over primes and proves each log
term nonnegative. It retains Mathlib's definition of theta, basic prime and
logarithm facts, finite sums and tactics. No general Chebyshev bound or PNT
is used in the displayed argument. A matching external build, axiom audit and
recursive declaration-dependency audit are still required.
-/

noncomputable section

namespace NativeThetaNonneg

/-- The actual theta function is nonnegative at every real argument. -/
theorem theta_sum_nonnegative (x : ℝ) : 0 ≤ Chebyshev.theta x := by
  unfold Chebyshev.theta
  apply Finset.sum_nonneg
  intro p hp
  have hprime : Nat.Prime p := (Finset.mem_filter.mp hp).2
  have hnat : 1 ≤ p := Nat.le_of_lt hprime.one_lt
  have hreal : (1 : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast hnat
  exact Real.log_nonneg hreal

end NativeThetaNonneg
