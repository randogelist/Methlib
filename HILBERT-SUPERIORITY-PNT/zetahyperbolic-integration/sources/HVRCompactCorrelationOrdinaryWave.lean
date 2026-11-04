import HVRCompactCorrelationFourierSquare

/-! Compact autocorrelation Fourier identity stated directly in terms of
the ordinary inverse Fourier integral. This avoids mentioning the Schwartz
wave object in the conclusion. External cached Lean compilation, theorem
axiom audit and controlled swap/convolution traces remain required. -/

noncomputable section
open MeasureTheory
open HVRPhysicalKernelCandidate HVRSpectralCorrelationCompact
open HVRZetaHyperbolicFrequencyBounds HVRCompactCorrelationFourierSquare

namespace HVRCompactCorrelationOrdinaryWave

/-- The exact compact-seed inverse-Fourier square identity, expressed without
the Schwartz-valued wave object. -/
theorem fourierInv_correlation_eq_seed_transform_sq
    (w : ℝ) (hw : 0 < w) (x : ℝ) :
    FourierTransformInv.fourierInv (complexCorrelation w hw) x =
      (FourierTransformInv.fourierInv (complexSeed w hw) x) ^ 2 := by
  calc
    FourierTransformInv.fourierInv (complexCorrelation w hw) x =
        ∫ t : ℝ, complexCorrelation w hw t * phase t (-2 * Real.pi * x) :=
      fourierInv_eq_phase_integral _ _
    _ = (∫ t : ℝ, complexSeed w hw t * phase t (-2 * Real.pi * x)) ^ 2 :=
      correlation_phase_integral_eq_square w hw _
    _ = (FourierTransformInv.fourierInv (complexSeed w hw) x) ^ 2 := by
      rw [fourierInv_eq_phase_integral]

end HVRCompactCorrelationOrdinaryWave
