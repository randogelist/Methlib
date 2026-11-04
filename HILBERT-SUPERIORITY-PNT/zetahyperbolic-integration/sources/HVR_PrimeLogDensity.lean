import NativeChebyshevBound
import HVR_PrimeCount_GrowthCandidate
import HVR_Smoothing_MonotoneNormalization

noncomputable section

/-! Actual log-prime mass in logarithmic coordinates. This module supplies
pointwise bounds for smoothing; it does not prove a convolution limit, a
Laplace identity, or the prime number theorem. Its Mathlib proof dependencies
still require the project's route-independence review. -/

namespace HVRPrimeLogDensity

open HVRMonotoneNormalization HVRPrimeCountMellin HVRPrimeCountGrowth

/-- The actual Chebyshev prime mass at exp t. -/
def logPrimeMass (t : ℝ) : ℝ := Chebyshev.theta (Real.exp t)

/-- The prime mass divided by exp t. -/
def logPrimeDensity (t : ℝ) : ℝ := normalizedMass logPrimeMass t

/-- This is the same prime sum used in the already audited Mellin bridge. -/
theorem logPrimeMass_eq_primeTheta (t : ℝ) :
    (logPrimeMass t : ℂ) = primeTheta (Real.exp t) := by
  exact (primeTheta_eq_chebyshev (Real.exp t)).symm

theorem logPrimeMass_monotone : Monotone logPrimeMass := by
  intro x y hxy
  exact Chebyshev.theta_mono (Real.exp_le_exp.mpr hxy)

theorem logPrimeDensity_nonneg (t : ℝ) : 0 ≤ logPrimeDensity t := by
  unfold logPrimeDensity normalizedMass logPrimeMass
  exact mul_nonneg (le_of_lt (Real.exp_pos (-t))) (Chebyshev.theta_nonneg _)

/-- The elementary Chebyshev bound makes the concrete density globally
bounded; no prime-number asymptotic is used in this step. -/
theorem logPrimeDensity_le_log_four (t : ℝ) :
    logPrimeDensity t ≤ Real.log 4 := by
  have ht : 0 ≤ Real.exp t := le_of_lt (Real.exp_pos t)
  unfold logPrimeDensity normalizedMass logPrimeMass
  calc
    Real.exp (-t) * Chebyshev.theta (Real.exp t) ≤
        Real.exp (-t) * (Real.log 4 * Real.exp t) :=
      mul_le_mul_of_nonneg_left (HVRNativeChebyshevBound.theta_le_log4_mul_x_native ht)
        (le_of_lt (Real.exp_pos (-t)))
    _ = (Real.exp (-t) * Real.exp t) * Real.log 4 := by ring
    _ = Real.log 4 := by rw [← Real.exp_add]; simp

/-- Concrete one-sided pointwise comparison for the prime density. -/
theorem logPrimeDensity_le {x y : ℝ} (hxy : x ≤ y) :
    logPrimeDensity x ≤ Real.exp (y - x) * logPrimeDensity y := by
  exact normalizedMass_le logPrimeMass logPrimeMass_monotone hxy

theorem weighted_logPrimeDensity_le {x y k : ℝ} (hxy : x ≤ y) (hk : 0 ≤ k) :
    k * logPrimeDensity x ≤ k * (Real.exp (y - x) * logPrimeDensity y) :=
  mul_le_mul_of_nonneg_left (logPrimeDensity_le hxy) hk

/-- Comparison with the value at a nonnegative backward shift. -/
theorem logPrimeDensity_past_le (x v : ℝ) (hv : 0 ≤ v) :
    logPrimeDensity (x - v) ≤ Real.exp v * logPrimeDensity x := by
  have h := logPrimeDensity_le (x := x - v) (y := x) (by linarith)
  have hshift : x - (x - v) = v := by ring
  simpa only [hshift] using h

/-- Comparison with the value at a nonnegative forward shift. -/
theorem logPrimeDensity_le_future (x v : ℝ) (hv : 0 ≤ v) :
    logPrimeDensity x ≤ Real.exp v * logPrimeDensity (x + v) := by
  have h := logPrimeDensity_le (x := x) (y := x + v) (by linarith)
  have hshift : x + v - x = v := by ring
  simpa only [hshift] using h

end HVRPrimeLogDensity
