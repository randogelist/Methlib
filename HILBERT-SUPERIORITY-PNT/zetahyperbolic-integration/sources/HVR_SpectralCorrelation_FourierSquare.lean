import HVR_SpectralCorrelation_Regularity
import HVR_PhysicalKernel_Candidate
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

noncomputable section
open MeasureTheory HVRSmoothingFrequencySeed HVRPhysicalKernelCandidate
open HVRSpectralSeedCorrelation HVRSpectralCorrelationCompact

/-! Candidate Fourier half of the spectral identity. For the real even seed,
complex autocorrelation equals the complex convolution, whose inverse Fourier
transform equals the square (not yet the squared norm) of the physical wave.
Real-valuedness of the wave and identification with rawKernel remain separate
obligations. No Lean was run locally. -/
namespace HVRSpectralCorrelationFourierSquare

theorem complexSeed_integrable (w : ℝ) (hw : 0 < w) :
    Integrable (complexSeed w hw) volume :=
  (complexSeed_smooth w hw).continuous.integrable_of_hasCompactSupport
    (complexSeed_compact w hw)

theorem complexCorrelation_eq_convolution (w : ℝ) (hw : 0 < w) :
    complexCorrelation w hw = MeasureTheory.convolution (complexSeed w hw)
      (complexSeed w hw) (ContinuousLinearMap.mul ℂ ℂ) volume := by
  funext t
  rw [MeasureTheory.convolution_mul]
  change (((∫ u : ℝ, seed w hw u * seed w hw (u - t)) : ℝ) : ℂ) =
    ∫ u : ℝ, ((seed w hw u : ℂ) * (seed w hw (t - u) : ℂ))
  rw [← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards [] with u
  rw [show t - u = -(u - t) by ring, seed_even]
  push_cast
  ring

theorem wave_eq_fourierInv_complexSeed (w : ℝ) (hw : 0 < w) (x : ℝ) :
    wave w hw x = FourierTransformInv.fourierInv (complexSeed w hw) x := by
  change (⇑(FourierTransformInv.fourierInv (seedSchwartz w hw))) x = _
  rw [SchwartzMap.fourierInv_coe]
  congr 1

/-- Exact inverse-Fourier correlation identity up to the wave-realness step. -/
theorem fourierInv_correlation_eq_wave_sq (w : ℝ) (hw : 0 < w) (x : ℝ) :
    FourierTransformInv.fourierInv (complexCorrelation w hw) x = (wave w hw x) ^ 2 := by
  calc
    FourierTransformInv.fourierInv (complexCorrelation w hw) x =
        FourierTransform.fourier (complexCorrelation w hw) (-x) :=
      Real.fourierInv_eq_fourier_neg _ _
    _ = FourierTransform.fourier (complexSeed w hw) (-x) *
          FourierTransform.fourier (complexSeed w hw) (-x) := by
      rw [complexCorrelation_eq_convolution]
      exact Real.fourier_mul_convolution_eq (complexSeed_integrable w hw)
        (complexSeed_integrable w hw) (-x)
    _ = (wave w hw x) ^ 2 := by
      rw [wave_eq_fourierInv_complexSeed, Real.fourierInv_eq_fourier_neg]
      ring

/-- The physical squared-norm identity, conditional on wave realness. -/
theorem fourierInv_correlation_eq_rawKernel_of_im_zero
    (w : ℝ) (hw : 0 < w) (x : ℝ) (hreal : (wave w hw x).im = 0) :
    FourierTransformInv.fourierInv (complexCorrelation w hw) x =
      (rawKernel w hw x : ℂ) := by
  have hz : wave w hw x = ((wave w hw x).re : ℂ) := by
    apply Complex.ext <;> simp [hreal]
  rw [fourierInv_correlation_eq_wave_sq, rawKernel, hz]
  simp [Complex.norm_real, Real.norm_eq_abs, sq_abs]

end HVRSpectralCorrelationFourierSquare
