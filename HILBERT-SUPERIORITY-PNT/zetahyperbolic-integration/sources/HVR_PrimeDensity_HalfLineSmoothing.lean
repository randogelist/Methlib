import HVR_HalfLine_IndicatorConvolution
import HVR_PrimeDensity_AbelGlueConditional
import HVR_PrimeDensity_ConcentratedSqueeze

noncomputable section
open Filter MeasureTheory
open scoped Topology
open HVRHalfLineIndicatorConvolution HVRPrimeDensitySpatialAbel
open HVRPrimeDensityConcentratedSqueeze
open HVRCorrectionBoundaryLimit HVRPrimeDensityFubiniBridge
open HVRPrimeBoundaryAbelLimitConditional HVRPrimeDensityAbelGlueConditional

/-!
Candidate conditional adapter from the audited half-line indicator limit and
prime-error convolution decay to smoothing limits. The explicit decomposition
identities and reflected-kernel properties are NOT proved here. The previously
audited conditional Abel glue can supply the error-decay inputs once its own
hypotheses have been discharged. No Lean was run locally.
-/
namespace HVRPrimeDensityHalfLineSmoothing

/-- A unit-mass half-line baseline plus a decaying complex error converges to one. -/
theorem smoothing_tendsto_one_of_halfLine_error
    (smooth : ℝ → ℝ) (k : ℝ → ℝ) (K : ℝ → ℂ)
    (hk : Integrable k volume) (hunit : (∫ v : ℝ, k v) = 1)
    (herror : Tendsto (undamped K) atTop (𝓝 0))
    (hidentity : ∀ x : ℝ,
      smooth x = halfLineConvolution k x + (undamped K x).re) :
    Tendsto smooth atTop (𝓝 1) := by
  have hreal : Tendsto (fun x : ℝ => (undamped K x).re) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Complex.zero_re] using
      (Complex.continuous_re.tendsto (0 : ℂ)).comp herror
  have hsum := (halfLineConvolution_tendsto_one k hk hunit).add hreal
  have heq : smooth = fun x : ℝ => halfLineConvolution k x + (undamped K x).re := by
    funext x
    exact hidentity x
  rw [heq]
  simpa only [add_zero] using hsum

/-- Forward and backward limits from explicit decompositions and error decay.
The reflected kernel can be chosen separately; no reflection identity or
Fourier representation is assumed silently. -/
theorem both_smoothing_limits_of_halfLine_errors
    (k kforward : ℝ → ℝ) (Kback Kforward : ℝ → ℂ)
    (hk : Integrable k volume) (hunit : (∫ v : ℝ, k v) = 1)
    (hkforward : Integrable kforward volume)
    (hunitforward : (∫ v : ℝ, kforward v) = 1)
    (hbackError : Tendsto (undamped Kback) atTop (𝓝 0))
    (hforwardError : Tendsto (undamped Kforward) atTop (𝓝 0))
    (hbackIdentity : ∀ x : ℝ,
      backwardSmooth k x = halfLineConvolution k x + (undamped Kback x).re)
    (hforwardIdentity : ∀ x : ℝ,
      forwardSmooth k x = halfLineConvolution kforward x + (undamped Kforward x).re) :
    Tendsto (forwardSmooth k) atTop (𝓝 1) ∧
      Tendsto (backwardSmooth k) atTop (𝓝 1) := by
  constructor
  · exact smoothing_tendsto_one_of_halfLine_error (forwardSmooth k) kforward Kforward
      hkforward hunitforward hforwardError hforwardIdentity
  · exact smoothing_tendsto_one_of_halfLine_error (backwardSmooth k) k Kback
      hk hunit hbackError hbackIdentity

/-- Combine the preceding limit adapter with the audited conditional Abel
glue. The decomposition and frequency-side bounds are explicit inputs. -/
theorem smoothing_tendsto_one_of_frequency_test
    (smooth : ℝ → ℝ) (k : ℝ → ℝ) (ψ : ℝ → ℂ) (C : ℝ)
    (hk : Integrable k volume) (hunit : (∫ v : ℝ, k v) = 1)
    (hψ : Integrable ψ volume) (hK : Integrable (kernel ψ) volume)
    (hcontinuous : Continuous ψ) (hcompact : HasCompactSupport ψ)
    (hmeas : ∀ x : ℝ, ∀ n : ℕ, AEStronglyMeasurable
      (frequencyIntegrand ψ x (boundaryEps n)) volume)
    (hdom : ∀ x : ℝ, ∀ n : ℕ, ∀ᵐ t : ℝ ∂volume,
      ‖frequencyIntegrand ψ x (boundaryEps n) t‖ ≤ C * ‖ψ t‖)
    (hidentity : ∀ x : ℝ,
      smooth x = halfLineConvolution k x + (undamped (kernel ψ) x).re) :
    Tendsto smooth atTop (𝓝 1) := by
  apply smoothing_tendsto_one_of_halfLine_error smooth k (kernel ψ) hk hunit
  · exact undamped_tendsto_zero_of_dominated ψ C hψ hK hcontinuous hcompact hmeas hdom
  · exact hidentity

end HVRPrimeDensityHalfLineSmoothing
