import HVRRealReflection
import HVR_PrimeDensity_HalfLineSmoothing
import Mathlib.MeasureTheory.Group.Integral

noncomputable section
open MeasureTheory

local instance : (volume : Measure ℝ).IsNegInvariant :=
  HVRRealReflection.real_volume_negInvariant_direct
open MeasureTheory HVRPrimeLogDensity HVRMonotoneNormalization

/-!
Candidate support lemmas for the smoothing decomposition. The actual prime
log-density vanishes on the nonpositive axis; its split into a strict-half-line
baseline and error is pointwise. The audited halfLineConvolution uses Ici,
which differs at zero: replacing Ioi by Ici requires an almost-everywhere
argument. The integral-level decomposition and frequency identification are
not asserted here. No local Lean run.
-/
namespace HVRPrimeDensitySmoothingDecomposition

/-- There are no primes below exp u when u is nonpositive. -/
theorem logPrimeDensity_zero_of_nonpos (u : ℝ) (hu : u ≤ 0) :
    logPrimeDensity u = 0 := by
  have hexp : Real.exp u ≤ 1 := Real.exp_le_one_iff.mpr hu
  have hlt : Real.exp u < 2 := lt_of_le_of_lt hexp (by norm_num)
  have htheta : Chebyshev.theta (Real.exp u) = 0 :=
    Chebyshev.theta_eq_zero_of_lt_two hlt
  simp only [logPrimeDensity, normalizedMass, logPrimeMass, htheta, mul_zero]

/-- Exact pointwise split with the strict positive half-line. -/
theorem logPrimeDensity_strict_indicator_decomposition (u : ℝ) :
    logPrimeDensity u =
      (Set.Ioi (0 : ℝ)).indicator (fun _ : ℝ => (1 : ℝ)) u +
      (Set.Ioi (0 : ℝ)).indicator (fun v : ℝ => logPrimeDensity v - 1) u := by
  by_cases hu : 0 < u
  · have hmem : u ∈ Set.Ioi (0 : ℝ) := hu
    simp only [Set.indicator_of_mem hmem]
    ring
  · have hle : u ≤ 0 := le_of_not_gt hu
    have hnot : u ∉ Set.Ioi (0 : ℝ) := hu
    simp only [Set.indicator_of_notMem hnot, zero_add,
      logPrimeDensity_zero_of_nonpos u hle]

/-- A function and its reflection have the same L1 property. -/
theorem reflectedKernel_integrable (k : ℝ → ℝ) (hk : Integrable k volume) :
    Integrable (fun v : ℝ => k (-v)) volume := hk.comp_neg

/-- Reflection preserves the total mass. -/
theorem reflectedKernel_integral (k : ℝ → ℝ) :
    (∫ v : ℝ, k (-v)) = ∫ v : ℝ, k v :=
  integral_neg_eq_self k volume

end HVRPrimeDensitySmoothingDecomposition
