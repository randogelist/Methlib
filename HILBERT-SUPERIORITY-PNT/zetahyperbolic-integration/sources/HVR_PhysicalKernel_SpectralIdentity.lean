import HVR_SpectralCorrelation_FourierSquare
import HVR_PhysicalKernel_WaveReal

noncomputable section
open HVRPhysicalKernelCandidate HVRSpectralCorrelationCompact
open HVRSpectralCorrelationFourierSquare HVRPhysicalKernelWaveReal

/-! Candidate discharge of wave-realness in the spectral identity. Further
frequency rescaling, concentration and prime smoothing limits remain open.
No Lean was run locally. -/
namespace HVRPhysicalKernelSpectralIdentity

theorem fourierInv_correlation_eq_rawKernel (w : ℝ) (hw : 0 < w) (x : ℝ) :
    FourierTransformInv.fourierInv (complexCorrelation w hw) x =
      (rawKernel w hw x : ℂ) :=
  fourierInv_correlation_eq_rawKernel_of_im_zero w hw x (wave_im_zero w hw x)

end HVRPhysicalKernelSpectralIdentity
