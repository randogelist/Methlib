import HVRRealReflection
import HVR_HalfLine_IndicatorConvolution
import HVR_PrimeDensity_SpatialAbel
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Set

noncomputable section
open MeasureTheory

local instance : (volume : Measure ℝ).IsNegInvariant :=
  HVRRealReflection.real_volume_negInvariant_direct
open MeasureTheory HVRHalfLineIndicatorConvolution

/-!
A-tier candidate: rewrite the audited half-line baseline in positive
log-coordinate u. The singleton {0} has measure zero, so the existing closed
indicator gives the same integral as the strict positive half-line. No Lean
was run locally; this candidate needs the external cached build and audit.
-/
namespace HVRPrimeDensityIndicatorIntegral

/-- The half-line baseline in the prime-density integration variable. -/
theorem halfLineConvolution_eq_Ioi (k : ℝ → ℝ) (x : ℝ) :
    halfLineConvolution k x = ∫ u : ℝ in Set.Ioi 0, k (x - u) := by
  let f : ℝ → ℝ := fun u => k (x - u) *
    (Set.Ici (0 : ℝ)).indicator (fun _ : ℝ => (1 : ℝ)) u
  calc
    halfLineConvolution k x = ∫ t : ℝ, f (x - t) := by
      unfold halfLineConvolution
      apply integral_congr_ae
      filter_upwards [] with t
      simp only [f, sub_sub_cancel]
    _ = ∫ u : ℝ, f u := integral_sub_left_eq_self f volume x
    _ = ∫ u : ℝ in Set.Ici 0, k (x - u) := by
      rw [← integral_indicator measurableSet_Ici]
      apply integral_congr_ae
      filter_upwards [] with u
      by_cases hu : u ∈ Set.Ici (0 : ℝ)
      · simp only [f, Set.indicator_of_mem hu, mul_one]
      · simp only [f, Set.indicator_of_notMem hu, mul_zero]
    _ = ∫ u : ℝ in Set.Ioi 0, k (x - u) := integral_Ici_eq_integral_Ioi

end HVRPrimeDensityIndicatorIntegral
