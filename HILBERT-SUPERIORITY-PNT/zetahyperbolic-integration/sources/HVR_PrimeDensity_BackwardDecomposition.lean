import HVRRealReflection
import HVR_PrimeDensity_IndicatorIntegral
import HVR_PrimeDensity_IntegralDecomposition
import HVR_PrimeDensity_WeightedIntegrability
import Mathlib.MeasureTheory.Group.Integral

noncomputable section
open MeasureTheory

local instance : (volume : Measure ℝ).IsNegInvariant :=
  HVRRealReflection.real_volume_negInvariant_direct
open Filter MeasureTheory
open HVRPrimeLogDensity HVRPrimeDensitySpatialAbel
open HVRPrimeDensityConcentratedSqueeze HVRPrimeDensityWeightedIntegrability
open HVRPrimeDensitySmoothingDecomposition HVRPrimeDensityIntegralDecomposition
open HVRHalfLineIndicatorConvolution HVRPrimeDensityIndicatorIntegral

/-!
Candidate full backward smoothing decomposition for any integrable real
kernel. The strict half-line ignores the zero endpoint, and the separately
staged indicator identity handles its difference from the closed baseline.
No local Lean execution or unconditional PNT claim.
-/
namespace HVRPrimeDensityBackwardDecomposition

/-- The actual backward average is its half-line baseline plus the real
actual prime-error convolution. -/
theorem backward_eq_halfLine_add_error (k : ℝ → ℝ) (hk : Integrable k volume) (x : ℝ) :
    backwardSmooth k x = halfLineConvolution k x +
      (undamped (fun v : ℝ => (k v : ℂ)) x).re := by
  have hshift : Integrable (fun u : ℝ => k (x - u)) volume := hk.comp_sub_left x
  have hshift' : IntegrableOn (fun u : ℝ => k (x - u)) (Set.Ioi 0) volume :=
    hshift.mono_measure Measure.restrict_le_self
  have hdensity : IntegrableOn (fun u : ℝ => k (x - u) * logPrimeDensity u)
      (Set.Ioi 0) volume := by
    exact weighted_density_integrableOn (fun u : ℝ => k (x - u)) id
      (Set.Ioi 0) hshift' measurable_id
  have herror : IntegrableOn (fun u : ℝ => (logPrimeDensity u - 1) * k (x - u))
      (Set.Ioi 0) volume := by
    apply (hdensity.sub hshift').congr
    filter_upwards [] with u
    simp only [Pi.sub_apply]
    ring
  have hchange : backwardSmooth k x = ∫ u : ℝ, k (x - u) * logPrimeDensity u := by
    unfold backwardSmooth
    simp only [setIntegral_univ]
    have h := integral_sub_left_eq_self
      (fun u : ℝ => k (x - u) * logPrimeDensity u) volume x
    simpa only [sub_sub_cancel] using h
  have hrestrict : (∫ u : ℝ, k (x - u) * logPrimeDensity u) =
      ∫ u : ℝ in Set.Ioi 0, k (x - u) * logPrimeDensity u := by
    rw [← integral_indicator measurableSet_Ioi]
    apply integral_congr_ae
    filter_upwards [] with u
    by_cases hu : 0 < u
    · simp only [Set.indicator_of_mem (show u ∈ Set.Ioi (0 : ℝ) from hu)]
    · have hle : u ≤ 0 := le_of_not_gt hu
      have hnot : u ∉ Set.Ioi (0 : ℝ) := hu
      simp only [Set.indicator_of_notMem hnot, logPrimeDensity_zero_of_nonpos u hle,
        mul_zero]
  rw [hchange, hrestrict, halfLineConvolution_eq_Ioi, undamped_ofReal_re]
  calc
    (∫ u : ℝ in Set.Ioi 0, k (x - u) * logPrimeDensity u) =
        ∫ u : ℝ in Set.Ioi 0,
          k (x - u) + (logPrimeDensity u - 1) * k (x - u) := by
      apply integral_congr_ae
      filter_upwards [] with u
      ring
    _ = _ := integral_add hshift' herror

/-- Forward smoothing uses the same identity for the reflected kernel. -/
theorem forward_eq_halfLine_add_reflected_error (k : ℝ → ℝ)
    (hk : Integrable k volume) (x : ℝ) :
    forwardSmooth k x = halfLineConvolution (fun v : ℝ => k (-v)) x +
      (undamped (fun v : ℝ => (k (-v) : ℂ)) x).re := by
  rw [forward_eq_backward_reflection]
  exact backward_eq_halfLine_add_error _ hk.comp_neg x

end HVRPrimeDensityBackwardDecomposition
