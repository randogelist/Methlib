import Mathlib.NumberTheory.Chebyshev
import Mathlib.Tactic

/-!
Candidate monotonicity proof for the actual Chebyshev theta function. This
uses inclusion of finite prime cutoffs and nonnegativity of logarithms of
natural numbers. It retains Mathlib's theta definition, natural floor,
finite-set and logarithm infrastructure. External compilation, theorem-level
axiom audit and recursive declaration-dependency inspection are required.
-/

noncomputable section

namespace NativeThetaMono

/-- Increasing the cutoff cannot decrease the prime-log sum. -/
theorem theta_monotone_from_cutoffs : Monotone Chebyshev.theta := by
  intro x y hxy
  unfold Chebyshev.theta
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.filter_subset_filter _
      (Finset.Ioc_subset_Ioc_right (Nat.floor_mono hxy))
  · intro p hp hpnot
    exact Real.log_natCast_nonneg p

end NativeThetaMono
