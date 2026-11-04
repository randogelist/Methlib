import HVR_PrimeDensity_SmoothingDecomposition
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

noncomputable section
open MeasureTheory HVRPrimeLogDensity HVRPrimeDensitySpatialAbel
open HVRPrimeDensityConcentratedSqueeze

/-!
Uncompiled candidate steps toward the integral smoothing decomposition.
Reflection gives the forward average as a backward average of the reflected
kernel.  The complex error convolution is precisely the real error integral
for real kernels.  No assertion is made that the full smoothing decomposition
holds; in particular, its strict/closed half-line a.e. step remains separate.
No Lean was run locally.
-/
namespace HVRPrimeDensityIntegralDecomposition

/-- Forward smoothing is backward smoothing with the reflected real kernel. -/
theorem forward_eq_backward_reflection (k : ℝ → ℝ) (x : ℝ) :
    forwardSmooth k x = backwardSmooth (fun v : ℝ => k (-v)) x := by
  unfold forwardSmooth backwardSmooth
  simp only [setIntegral_univ]
  have h := integral_neg_eq_self
    (fun v : ℝ => k (-v) * logPrimeDensity (x - v)) volume
  simpa only [neg_neg, sub_neg_eq_add] using h

/-- The actual prime-error convolution for a real kernel has real part equal to
its real-valued half-line error integral. -/
theorem undamped_ofReal_re (k : ℝ → ℝ) (x : ℝ) :
    (undamped (fun v : ℝ => (k v : ℂ)) x).re =
      ∫ u : ℝ in Set.Ioi 0, (logPrimeDensity u - 1) * k (x - u) := by
  unfold undamped
  have heq : (∫ u : ℝ in Set.Ioi 0,
      (((logPrimeDensity u - 1) * k (x - u) : ℝ) : ℂ)) =
      (((∫ u : ℝ in Set.Ioi 0, (logPrimeDensity u - 1) * k (x - u)) : ℝ) : ℂ) :=
    integral_complex_ofReal
  simp only [← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_mul]
  rw [heq]
  simp only [Complex.ofReal_re]

end HVRPrimeDensityIntegralDecomposition
