import HVR_PhysicalKernel_TailScaling
import HVR_PrimeDensity_ScaledSpectrumDecay
import HVR_PrimeDensity_SmoothingDecomposition
import HVR_PrimeDensity_PNTConditional

noncomputable section
open Filter MeasureTheory
open scoped Topology
open HVRPhysicalKernelScaledTranslate HVRPhysicalKernelTailScaling
open HVRPhysicalKernelCanonicalWindow HVRPhysicalKernelScaledSpectrum
open HVRPrimeDensityScaledSpectrumDecay HVRPrimeDensityHalfLineSmoothing
open HVRPrimeDensitySmoothingDecomposition HVRPrimeDensityConcentratedSqueeze
open HVRHalfLineIndicatorConvolution HVRPrimeDensitySpatialAbel
open HVRPrimeDensityFubiniBridge HVRPrimeDensityPNTConditional

/-!
Candidate conditional assembly for the exact theta ratio. Its stated input
includes integrability of the two inverse-frequency kernels and the explicit
forward/backward smoothing decompositions. None of those assumptions are
silently discharged here. The concentration bounds and individual frequency
error limits are supplied by already audited modules. The result does not
establish unconditional PNT or route independence. No local Lean execution.
-/
namespace HVRPrimeDensityScaledConditionalEndpoint

/-- The two explicit inverse-frequency integrability and smoothing identities
needed for this scaled kernel at every positive scale and translation. -/
def ScaledSmoothingData (w : ℝ) (hw : 0 < w) : Prop :=
  ∀ (N c : ℝ), 0 < N →
    Integrable (kernel (scaledSpectrum w hw N c)) volume ∧
    Integrable (kernel (scaledSpectrum w hw N (-c))) volume ∧
    (∀ x : ℝ,
      backwardSmooth (scaledTranslate w hw N c) x =
        halfLineConvolution (scaledTranslate w hw N c) x +
          (undamped (kernel (scaledSpectrum w hw N c)) x).re) ∧
    (∀ x : ℝ,
      forwardSmooth (scaledTranslate w hw N c) x =
        halfLineConvolution (fun v : ℝ => scaledTranslate w hw N c (-v)) x +
          (undamped (kernel (scaledSpectrum w hw N (-c))) x).re)

/-- The scaled data imply both actual-density smoothing limits. -/
theorem scaled_smoothing_limits_of_data (w : ℝ) (hw : 0 < w)
    (hdata : ScaledSmoothingData w hw) (N c : ℝ) (hN : 0 < N) :
    Tendsto (forwardSmooth (scaledTranslate w hw N c)) atTop (𝓝 1) ∧
    Tendsto (backwardSmooth (scaledTranslate w hw N c)) atTop (𝓝 1) := by
  obtain ⟨hKb, hKf, hback, hforward⟩ := hdata N c hN
  have hk : Integrable (scaledTranslate w hw N c) volume :=
    scaledTranslate_integrable w hw N c hN
  have hm : (∫ v : ℝ, scaledTranslate w hw N c v) = 1 :=
    scaledTranslate_integral w hw N c hN
  have hrf : Integrable (fun v : ℝ => scaledTranslate w hw N c (-v)) volume :=
    reflectedKernel_integrable _ hk
  have hrm : (∫ v : ℝ, scaledTranslate w hw N c (-v)) = 1 := by
    rw [reflectedKernel_integral, hm]
  have heb := scaledSpectrum_undamped_tendsto_zero w hw N c hN hKb
  have hef := scaledSpectrum_undamped_tendsto_zero w hw N (-c) hN hKf
  exact both_smoothing_limits_of_halfLine_errors
    (scaledTranslate w hw N c) (fun v : ℝ => scaledTranslate w hw N c (-v))
    (kernel (scaledSpectrum w hw N c)) (kernel (scaledSpectrum w hw N (-c)))
    hk hm hrf hrm heb hef hback hforward

/-- Exact theta-ratio endpoint conditional on the explicitly stated scaled
smoothing data. No claim is made that the data have been proved. -/
theorem theta_ratio_tendsto_one_of_scaled_smoothing_data
    (w : ℝ) (hw : 0 < w) (hdata : ScaledSmoothingData w hw) :
    Tendsto (fun x : ℝ => Chebyshev.theta x / x) atTop (𝓝 1) := by
  apply theta_ratio_tendsto_one_of_concentrated_smoothing
  intro δ hδ hδ1
  obtain ⟨N, hN, hnonneg, hki, hleft, hright, htail⟩ :=
    exists_concentrated_scaled_kernel w hw δ hδ
  have hlimits := scaled_smoothing_limits_of_data w hw hdata N (canonicalWindow δ / 2) hN
  exact ⟨canonicalWindow δ, scaledTranslate w hw N (canonicalWindow δ / 2),
    hnonneg, hki, hleft, hright, htail, hlimits.1, hlimits.2⟩

end HVRPrimeDensityScaledConditionalEndpoint
