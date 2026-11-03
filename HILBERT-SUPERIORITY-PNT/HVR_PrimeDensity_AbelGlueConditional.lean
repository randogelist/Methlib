import HVR_PrimeDensity_SpatialAbel
import HVR_PrimeBoundary_AbelLimitConditional

noncomputable section
open Filter MeasureTheory
open scoped Topology
open HVRCorrectionBoundaryLimit HVRPrimeDensityFubiniBridge
open HVRPrimeDensityFubiniIntegrable HVRPrimeDensitySpatialAbel
open HVRPrimeBoundaryAbelLimitConditional HVRPrimeBoundaryOrdinaryFrequencyDecay

/-!
Candidate identification of the undamped actual prime-density convolution
with the boundary frequency integral. Integrability of the physical kernel
and the frequency-side domination and measurability hypotheses are explicit.
This does not construct the required positive concentrated kernel, discharge
frequency domination, establish independence, or prove PNT. No local Lean run.
-/
namespace HVRPrimeDensityAbelGlueConditional

/-- The actual undamped spatial convolution equals the frequency boundary
integral when both sides admit the stated Abel limit. -/
theorem undamped_eq_ordinaryBoundary_of_dominated
    (ψ : ℝ → ℂ) (x C : ℝ)
    (hψ : Integrable ψ volume) (hK : Integrable (kernel ψ) volume)
    (hmeas : ∀ n : ℕ, AEStronglyMeasurable
      (frequencyIntegrand ψ x (boundaryEps n)) volume)
    (hdom : ∀ n : ℕ, ∀ᵐ t : ℝ ∂volume,
      ‖frequencyIntegrand ψ x (boundaryEps n) t‖ ≤ C * ‖ψ t‖) :
    undamped (kernel ψ) x = ordinaryBoundary ψ x := by
  have hs := spatial_abel_tendsto (kernel ψ) hK x
  have hf := frequency_integral_tendsto_boundary_of_dominated ψ x C hψ hmeas hdom
  have heq : ∀ n : ℕ,
      (∫ u : ℝ in Set.Ioi 0,
        dampedError (boundaryEps n) u * kernel ψ (x - u)) =
      (∫ t : ℝ, frequencyIntegrand ψ x (boundaryEps n) t) := by
    intro n
    simpa only [frequencyIntegrand] using
      abel_smoothing_eq_frequency_integral_of_integrable ψ (boundaryEps n) x hψ
        (boundaryEps_pos n)
  have hf' : Tendsto (fun n : ℕ => ∫ u : ℝ in Set.Ioi 0,
      dampedError (boundaryEps n) u * kernel ψ (x - u)) atTop
      (𝓝 (ordinaryBoundary ψ x)) := by
    apply hf.congr'
    filter_upwards [] with n
    exact (heq n).symm
  exact tendsto_nhds_unique hs hf'

/-- Under the same explicit hypotheses at every x, the actual undamped prime
error convolution tends to zero as x tends to positive infinity. -/
theorem undamped_tendsto_zero_of_dominated
    (ψ : ℝ → ℂ) (C : ℝ) (hψ : Integrable ψ volume)
    (hK : Integrable (kernel ψ) volume)
    (hcontinuous : Continuous ψ) (hcompact : HasCompactSupport ψ)
    (hmeas : ∀ x : ℝ, ∀ n : ℕ, AEStronglyMeasurable
      (frequencyIntegrand ψ x (boundaryEps n)) volume)
    (hdom : ∀ x : ℝ, ∀ n : ℕ, ∀ᵐ t : ℝ ∂volume,
      ‖frequencyIntegrand ψ x (boundaryEps n) t‖ ≤ C * ‖ψ t‖) :
    Tendsto (undamped (kernel ψ)) atTop (𝓝 0) := by
  have heq : undamped (kernel ψ) = ordinaryBoundary ψ := by
    funext x
    exact undamped_eq_ordinaryBoundary_of_dominated ψ x C hψ hK (hmeas x) (hdom x)
  rw [heq]
  exact ordinaryBoundary_tendsto_zero ψ hcontinuous hcompact

end HVRPrimeDensityAbelGlueConditional
