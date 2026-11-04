import HVRCompactCorrelationOrdinaryWave
import HVR_PhysicalKernel_WaveReal

noncomputable section
open HVRPhysicalKernelCandidate HVRSpectralCorrelationCompact

/-! Candidate physical spectral identity using the direct ordinary wave and
the audited finite-grid autocorrelation identity. The old Schwartz-valued
wave remains available, but is not used in this theorem. External Lean
compilation, theorem-level axiom audit and root dependency tracing are needed. -/
namespace HVRPhysicalKernelSpectralIdentity

theorem fourierInv_correlation_eq_rawKernel (w : ℝ) (hw : 0 < w) (x : ℝ) :
    FourierTransformInv.fourierInv (complexCorrelation w hw) x =
      (rawKernel w hw x : ℂ) := by
  have heq : FourierTransformInv.fourierInv (complexSeed w hw) x =
      HVROrdinarySeedWave.ordinaryWave w hw x := by
    simpa only [HVRPhysicalKernelCandidate.complexSeed, HVROrdinarySeed.complexSeed] using
      (HVROrdinarySeedWave.ordinaryWave_eq_fourierInv w hw x).symm
  have hreal := HVRPhysicalKernelWaveReal.ordinaryWave_im_zero w hw x
  have hz : HVROrdinarySeedWave.ordinaryWave w hw x =
      ((HVROrdinarySeedWave.ordinaryWave w hw x).re : ℂ) := by
    apply Complex.ext <;> simp [hreal]
  calc
    FourierTransformInv.fourierInv (complexCorrelation w hw) x =
        (FourierTransformInv.fourierInv (complexSeed w hw) x) ^ 2 :=
      HVRCompactCorrelationOrdinaryWave.fourierInv_correlation_eq_seed_transform_sq w hw x
    _ = (rawKernel w hw x : ℂ) := by
      rw [heq, rawKernel, hz]
      simp [Complex.norm_real, Real.norm_eq_abs, sq_abs]

end HVRPhysicalKernelSpectralIdentity
