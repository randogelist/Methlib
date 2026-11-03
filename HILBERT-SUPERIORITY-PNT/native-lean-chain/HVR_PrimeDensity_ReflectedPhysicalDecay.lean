import HVR_PrimeDensity_ReflectedSpectrum
import HVR_PrimeDensity_ScaledPhysicalDecay

noncomputable section
open Filter MeasureTheory
open scoped Topology
open HVRPrimeDensityFubiniBridge HVRPrimeDensitySpatialAbel
open HVRPrimeDensityReflectedSpectrum HVRPrimeDensityScaledPhysicalDecay
open HVRPhysicalKernelScaledSpectrum HVRPhysicalKernelScaledTranslate
open HVRPhysicalKernelScaledRepresentation

/-!
Candidate for the reflected physical-kernel prime-error limit. It combines
the externally audited spectrum-reflection and scaled-kernel representation.
It does not assert a smoothing decomposition, PNT, or route independence.
No local Lean execution was performed; external build and named audits are
required for this candidate.
-/
namespace HVRPrimeDensityReflectedPhysicalDecay

/-- The inverse kernel of the reflected frequency test is the reflection of
the very same scaled physical kernel. -/
theorem reflectedSpectrum_kernel_eq_reflectedPhysical
    (w : ℝ) (hw : 0 < w) (N c : ℝ) (hN : 0 < N) :
    kernel (reflectFrequency (scaledSpectrum w hw N c)) =
      (fun x : ℝ => (scaledTranslate w hw N c (-x) : ℂ)) := by
  funext x
  rw [kernel_reflectFrequency]
  exact kernel_scaledSpectrum_eq_scaledTranslate w hw N c (-x) hN

/-- Actual prime error convolved with the reflected scaled physical kernel
tends to zero. The smoothing-baseline identity is a separate obligation. -/
theorem reflectedPhysical_undamped_tendsto_zero
    (w : ℝ) (hw : 0 < w) (N c : ℝ) (hN : 0 < N) :
    Tendsto (undamped (fun x : ℝ => (scaledTranslate w hw N c (-x) : ℂ)))
      atTop (𝓝 0) := by
  have h := reflected_scaledSpectrum_undamped_tendsto_zero w hw N c hN
    (scaledSpectrum_inverseKernel_integrable w hw N c hN)
  rw [reflectedSpectrum_kernel_eq_reflectedPhysical w hw N c hN] at h
  exact h

end HVRPrimeDensityReflectedPhysicalDecay
