import HVR_SpectralCorrelation_Compact
import Mathlib.Analysis.Convolution

noncomputable section
open MeasureTheory HVRSmoothingFrequencySeed HVRSpectralSeedCorrelation

/-! Candidate bridge identifying the actual even seed autocorrelation with
its convolution, then deriving continuity and integrability. The later Fourier
identification with the physical squared kernel remains unproved. No local
Lean was executed. -/
namespace HVRSpectralCorrelationRegularity

theorem correlation_eq_convolution (w : ℝ) (hw : 0 < w) :
    correlation w hw = MeasureTheory.convolution (seed w hw) (seed w hw)
      (ContinuousLinearMap.mul ℝ ℝ) volume := by
  funext t
  rw [MeasureTheory.convolution_mul]
  unfold correlation
  apply integral_congr_ae
  filter_upwards [] with u
  have heq : t - u = -(u - t) := by ring
  rw [heq, seed_even]

theorem correlation_continuous (w : ℝ) (hw : 0 < w) :
    Continuous (correlation w hw) := by
  rw [correlation_eq_convolution]
  exact (seed_compact w hw).continuous_convolution_right
    (ContinuousLinearMap.mul ℝ ℝ) (seed_integrable w hw).locallyIntegrable
    (seed_smooth_Cinfty w hw).continuous

theorem correlation_integrable (w : ℝ) (hw : 0 < w) :
    Integrable (correlation w hw) volume := by
  rw [correlation_eq_convolution]
  exact MeasureTheory.Integrable.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ)
    (seed_integrable w hw) (seed_integrable w hw)

end HVRSpectralCorrelationRegularity
