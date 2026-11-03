import HVR_PrimeDensity_ReflectedPhysicalDecay
import HVR_PhysicalKernel_TailScaling
import HVR_PrimeDensity_IntegralDecomposition
import HVR_PrimeDensity_PNTConditional

noncomputable section
open Filter MeasureTheory
open scoped Topology
open HVRPrimeDensitySpatialAbel HVRPrimeDensityConcentratedSqueeze
open HVRHalfLineIndicatorConvolution HVRPrimeDensityHalfLineSmoothing
open HVRPrimeDensityIntegralDecomposition HVRPrimeDensitySmoothingDecomposition
open HVRPhysicalKernelScaledTranslate HVRPhysicalKernelTailScaling
open HVRPhysicalKernelCanonicalWindow HVRPrimeDensityScaledPhysicalDecay
open HVRPrimeDensityReflectedPhysicalDecay HVRPrimeDensityPNTConditional

/-!
Candidate narrowing of the conditional theta endpoint to a single explicitly
stated real-integral decomposition premise. Existing audited results supply the
numeric concentration, physical-kernel error decay, reflected error decay and
half-line baseline. BackwardDecomposition is not asserted unconditionally here.
No local Lean execution. Dependency independence is unverified.
-/
namespace HVRPrimeDensityDecompositionEndpoint

/-- The sole analytic identity still assumed by this conditional endpoint. -/
def BackwardDecomposition : Prop :=
  ∀ (k : ℝ → ℝ), Integrable k volume → ∀ x : ℝ,
    backwardSmooth k x = halfLineConvolution k x +
      (undamped (fun v : ℝ => (k v : ℂ)) x).re

/-- Scaled actual kernels have both smoothing limits when the decomposition
identity is supplied for integrable real kernels. -/
theorem scaled_smoothing_limits_of_backward_decomposition
    (hdecomp : BackwardDecomposition) (w : ℝ) (hw : 0 < w)
    (N c : ℝ) (hN : 0 < N) :
    Tendsto (forwardSmooth (scaledTranslate w hw N c)) atTop (𝓝 1) ∧
    Tendsto (backwardSmooth (scaledTranslate w hw N c)) atTop (𝓝 1) := by
  let k : ℝ → ℝ := scaledTranslate w hw N c
  have hk : Integrable k volume := scaledTranslate_integrable w hw N c hN
  have hm : (∫ v : ℝ, k v) = 1 := scaledTranslate_integral w hw N c hN
  have hkr : Integrable (fun v : ℝ => k (-v)) volume := reflectedKernel_integrable k hk
  have hmr : (∫ v : ℝ, k (-v)) = 1 := by
    rw [reflectedKernel_integral, hm]
  have hb : ∀ x : ℝ,
      backwardSmooth k x = halfLineConvolution k x +
        (undamped (fun v : ℝ => (k v : ℂ)) x).re := hdecomp k hk
  have hf : ∀ x : ℝ,
      forwardSmooth k x = halfLineConvolution (fun v : ℝ => k (-v)) x +
        (undamped (fun v : ℝ => (k (-v) : ℂ)) x).re := by
    intro x
    rw [forward_eq_backward_reflection]
    exact hdecomp (fun v : ℝ => k (-v)) hkr x
  have heb : Tendsto (undamped (fun v : ℝ => (k v : ℂ))) atTop (𝓝 0) :=
    scaledPhysical_undamped_tendsto_zero w hw N c hN
  have hef : Tendsto (undamped (fun v : ℝ => (k (-v) : ℂ))) atTop (𝓝 0) :=
    reflectedPhysical_undamped_tendsto_zero w hw N c hN
  exact both_smoothing_limits_of_halfLine_errors k (fun v : ℝ => k (-v))
    (fun v : ℝ => (k v : ℂ)) (fun v : ℝ => (k (-v) : ℂ))
    hk hm hkr hmr heb hef hb hf

/-- Exact theta-ratio limit conditional only on the explicitly named backward
integral decomposition. This does not claim independence or PNT closure. -/
theorem theta_ratio_tendsto_one_of_backward_decomposition
    (hdecomp : BackwardDecomposition) :
    Tendsto (fun x : ℝ => Chebyshev.theta x / x) atTop (𝓝 1) := by
  apply theta_ratio_tendsto_one_of_concentrated_smoothing
  intro δ hδ hδ1
  have hw : (0 : ℝ) < 1 := by norm_num
  obtain ⟨N, hN, hnonneg, hki, hleft, hright, htail⟩ :=
    exists_concentrated_scaled_kernel 1 hw δ hδ
  have hlimits := scaled_smoothing_limits_of_backward_decomposition hdecomp 1 hw
    N (canonicalWindow δ / 2) hN
  exact ⟨canonicalWindow δ, scaledTranslate 1 hw N (canonicalWindow δ / 2),
    hnonneg, hki, hleft, hright, htail, hlimits.1, hlimits.2⟩

end HVRPrimeDensityDecompositionEndpoint
