import HVR_PrimeBoundary_EventualAbelGlue
import HVR_PrimeBoundary_FrequencyMeasurable

noncomputable section
open Filter MeasureTheory
open scoped Topology
open HVRCorrectionBoundaryLimit HVRPrimeDensityFubiniBridge HVRPrimeDensitySpatialAbel
open HVRPrimeBoundaryOrdinaryFrequencyDecay HVRPrimeBoundaryEventualAbelGlue
open HVRPrimeBoundaryFrequencyMeasurable

/-! Candidate discharge of both frequency-side domination and measurability.
The inverse kernel's L1 integrability and compact-support witness stay explicit.
No local Lean run; no PNT or kernel-concentration claim. -/
namespace HVRPrimeBoundaryCompactGlue

theorem undamped_eq_ordinaryBoundary_of_compact
    (ψ : ℝ → ℂ) (x : ℝ) (K : Set ℝ) (hK : IsCompact K)
    (hsupport : ∀ t : ℝ, ψ t ≠ 0 → t ∈ K)
    (hψ : Integrable ψ volume) (hkernel : Integrable (kernel ψ) volume) :
    undamped (kernel ψ) x = ordinaryBoundary ψ x := by
  apply undamped_eq_ordinaryBoundary_of_compact_support ψ x K hK hsupport hψ hkernel
  intro n
  exact frequencyIntegrand_aestronglyMeasurable ψ (boundaryEps n) x hψ (boundaryEps_pos n)

theorem undamped_tendsto_zero_of_compact
    (ψ : ℝ → ℂ) (K : Set ℝ) (hK : IsCompact K)
    (hsupport : ∀ t : ℝ, ψ t ≠ 0 → t ∈ K)
    (hψ : Integrable ψ volume) (hkernel : Integrable (kernel ψ) volume)
    (hcontinuous : Continuous ψ) (hcompact : HasCompactSupport ψ) :
    Tendsto (undamped (kernel ψ)) atTop (𝓝 0) := by
  have heq : undamped (kernel ψ) = ordinaryBoundary ψ := by
    funext x
    exact undamped_eq_ordinaryBoundary_of_compact ψ x K hK hsupport hψ hkernel
  rw [heq]
  exact ordinaryBoundary_tendsto_zero ψ hcontinuous hcompact

end HVRPrimeBoundaryCompactGlue
