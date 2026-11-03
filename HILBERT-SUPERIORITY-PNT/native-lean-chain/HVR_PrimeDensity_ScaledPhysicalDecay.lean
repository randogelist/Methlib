import HVR_PhysicalKernel_ScaledRepresentation
import HVR_PrimeDensity_ScaledSpectrumDecay

noncomputable section
open Filter MeasureTheory
open scoped Topology
open HVRPhysicalKernelScaledRepresentation HVRPhysicalKernelScaledSpectrum
open HVRPhysicalKernelScaledTranslate HVRPrimeDensityScaledSpectrumDecay
open HVRPrimeDensityFubiniBridge HVRPrimeDensitySpatialAbel

/-!
Candidate discharge of the inverse-kernel L1 premise for the actual scaled
physical kernel, and application to prime-error decay. This depends on the
uncompiled scaled representation candidate. No local Lean was run.
It does not yet prove the reflected smoothing decomposition or PNT.
-/
namespace HVRPrimeDensityScaledPhysicalDecay

theorem scaledSpectrum_inverseKernel_integrable
    (w : ℝ) (hw : 0 < w) (N c : ℝ) (hN : 0 < N) :
    Integrable (kernel (scaledSpectrum w hw N c)) volume := by
  have heq : kernel (scaledSpectrum w hw N c) =
      (fun x : ℝ => (scaledTranslate w hw N c x : ℂ)) := by
    funext x
    exact kernel_scaledSpectrum_eq_scaledTranslate w hw N c x hN
  rw [heq]
  exact (scaledTranslate_integrable w hw N c hN).ofReal

/-- The actual prime-density error convolved with the scaled physical kernel
converges to zero, provided the candidate representation compiles. -/
theorem scaledPhysical_undamped_tendsto_zero
    (w : ℝ) (hw : 0 < w) (N c : ℝ) (hN : 0 < N) :
    Tendsto (undamped (fun x : ℝ => (scaledTranslate w hw N c x : ℂ)))
      atTop (𝓝 0) := by
  have h := scaledSpectrum_undamped_tendsto_zero w hw N c hN
    (scaledSpectrum_inverseKernel_integrable w hw N c hN)
  have heq : kernel (scaledSpectrum w hw N c) =
      (fun x : ℝ => (scaledTranslate w hw N c x : ℂ)) := by
    funext x
    exact kernel_scaledSpectrum_eq_scaledTranslate w hw N c x hN
  rw [heq] at h
  exact h

end HVRPrimeDensityScaledPhysicalDecay
