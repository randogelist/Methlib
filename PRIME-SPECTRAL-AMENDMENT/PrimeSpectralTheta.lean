import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

/-!
Finite-coordinate form of the theta spectral cutoff.  This module uses the
actual Mathlib von Mangoldt function and Chebyshev theta, and does not import
the project's PNT chain.  The finite sum is the coordinate expansion of the
proposed diagonal matrix element; an infinite-dimensional operator/inner
product identification is a separate obligation, not asserted here.
-/

noncomputable section
open scoped BigOperators

namespace PrimeSpectralTheta

/-- The proposed vector coordinate, for arbitrary real spectral shift. -/
def amplitude (sigma : ℝ) (n : ℕ) : ℝ :=
  Real.sqrt (ArithmeticFunction.vonMangoldt n) *
    Real.exp (-(sigma * Real.log (n : ℝ)) / 2)

/-- The diagonal factor of the unweighting operator `exp (sigma * A)`. -/
def unweight (sigma : ℝ) (n : ℕ) : ℝ :=
  Real.exp (sigma * Real.log (n : ℝ))

/-- Prime-projected cutoff matrix element, expanded in coordinates. -/
def cutoffPairing (sigma x : ℝ) : ℝ :=
  ∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter Nat.Prime,
    amplitude sigma n * (unweight sigma n * amplitude sigma n)

/-- At every prime, the two vector weights cancel the diagonal unweighting. -/
theorem prime_coordinate_cancellation (sigma : ℝ) {n : ℕ}
    (hn : Nat.Prime n) :
    amplitude sigma n * (unweight sigma n * amplitude sigma n) =
      Real.log (n : ℝ) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.one_le
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
  have hsqrt : Real.sqrt (Real.log (n : ℝ)) * Real.sqrt (Real.log (n : ℝ)) =
      Real.log (n : ℝ) := by
    nlinarith [Real.sq_sqrt hlog]
  have hexp :
      (Real.exp (-(sigma * Real.log (n : ℝ)) / 2) *
        Real.exp (-(sigma * Real.log (n : ℝ)) / 2)) *
          Real.exp (sigma * Real.log (n : ℝ)) = 1 := by
    rw [← Real.exp_add, ← Real.exp_add]
    have harg : -(sigma * Real.log (n : ℝ)) / 2 +
        -(sigma * Real.log (n : ℝ)) / 2 + sigma * Real.log (n : ℝ) = 0 := by ring
    rw [harg, Real.exp_zero]
  unfold amplitude unweight
  rw [ArithmeticFunction.vonMangoldt_apply_prime hn]
  calc
    (Real.sqrt (Real.log (n : ℝ)) * Real.exp (-(sigma * Real.log (n : ℝ)) / 2)) *
        (Real.exp (sigma * Real.log (n : ℝ)) *
          (Real.sqrt (Real.log (n : ℝ)) * Real.exp (-(sigma * Real.log (n : ℝ)) / 2))) =
      (Real.sqrt (Real.log (n : ℝ)) * Real.sqrt (Real.log (n : ℝ))) *
        ((Real.exp (-(sigma * Real.log (n : ℝ)) / 2) *
          Real.exp (-(sigma * Real.log (n : ℝ)) / 2)) *
            Real.exp (sigma * Real.log (n : ℝ))) := by ring
    _ = Real.log (n : ℝ) := by rw [hsqrt, hexp, mul_one]

/-- Exact finite prime-projected spectral cutoff for the actual theta. -/
theorem cutoffPairing_eq_chebyshev_theta (sigma x : ℝ) :
    cutoffPairing sigma x = Chebyshev.theta x := by
  unfold cutoffPairing Chebyshev.theta
  apply Finset.sum_congr rfl
  intro n hn
  exact prime_coordinate_cancellation sigma (Finset.mem_filter.mp hn).2

end PrimeSpectralTheta
