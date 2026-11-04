import HVRCompactCorrelationRegularity
import HVRCompactCorrelationPhaseSum
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
Candidate finite-grid derivation of the exact Fourier-square identity for
the HVR compact seed. The proof combines two one-variable limits and a finite
sum of one-variable translations. It is not the general Fourier convolution
theorem. External Lean compilation, named axiom audit, and controlled
transitive swap/convolution-target tracing are required.
-/

noncomputable section
open Filter MeasureTheory
open HVRSmoothingFrequencySeed HVRPhysicalKernelCandidate
open HVRSpectralSeedCorrelation HVRSpectralCorrelationCompact
open HVRZetaHyperbolicFrequencyBounds HVRCompactCorrelationQuadrature
open HVRCompactCorrelationRegularity HVRCompactCorrelationPhaseSum
open scoped Topology

namespace HVRCompactCorrelationFourierSquare

/-- The seed autocorrelation's phase integral is the square of the seed
phase integral, proved as the common limit of the same finite-grid sums. -/
theorem correlation_phase_integral_eq_square (w : ℝ) (hw : 0 < w) (ξ : ℝ) :
    (∫ t : ℝ, complexCorrelation w hw t * phase t ξ) =
      (∫ t : ℝ, complexSeed w hw t * phase t ξ) ^ 2 := by
  have hleft := sampled_frequency_integral_tendsto_interval_direct w hw ξ
  have hright := sampled_phase_integrals_tendsto_square w hw ξ
  have hlim := tendsto_nhds_unique hleft hright
  have hfull : (∫ t : ℝ in Set.Ioc (-w) w,
      complexCorrelation w hw t * phase t ξ) =
      ∫ t : ℝ, complexCorrelation w hw t * phase t ξ := by
    apply setIntegral_eq_integral_of_ae_compl_eq_zero
    filter_upwards [] with t ht
    have hband : w ≤ |t| := by
      by_contra hn
      have hlt : |t| < w := lt_of_not_ge hn
      have ht' := abs_lt.mp hlt
      exact ht ⟨ht'.1, le_of_lt ht'.2⟩
    simp only [complexCorrelation, Function.comp_apply,
      correlation_zero_of_band w hw t hband, Complex.ofReal_zero, zero_mul]
  rw [hfull] at hlim
  exact hlim

/-- The project's elementary phase agrees with Mathlib's inverse Fourier
normalization after the explicit factor 2π. -/
theorem fourierInv_eq_phase_integral (f : ℝ → ℂ) (x : ℝ) :
    FourierTransformInv.fourierInv f x =
      ∫ t : ℝ, f t * phase t (-2 * Real.pi * x) := by
  rw [Real.fourierInv_eq']
  apply integral_congr_ae
  filter_upwards [] with t
  simp only [Real.inner_apply, smul_eq_mul]
  have hphase : Complex.exp (((2 * Real.pi * (t * x) : ℝ) : ℂ) * Complex.I) =
      phase t (-2 * Real.pi * x) := by
    unfold phase
    congr 1
    push_cast
    ring
  rw [hphase, mul_comm]

/-- The physical wave is the inverse transform of the actual complex seed. -/
theorem wave_eq_fourierInv_seed (w : ℝ) (hw : 0 < w) (x : ℝ) :
    wave w hw x = FourierTransformInv.fourierInv (complexSeed w hw) x := by
  change (⇑(FourierTransformInv.fourierInv (seedSchwartz w hw))) x = _
  rw [SchwartzMap.fourierInv_coe]
  congr 1

/-- Exact target signature required by the physical-kernel PNT chain. -/
theorem fourierInv_correlation_eq_wave_sq_direct
    (w : ℝ) (hw : 0 < w) (x : ℝ) :
    FourierTransformInv.fourierInv (complexCorrelation w hw) x =
      (wave w hw x) ^ 2 := by
  calc
    FourierTransformInv.fourierInv (complexCorrelation w hw) x =
        ∫ t : ℝ, complexCorrelation w hw t * phase t (-2 * Real.pi * x) :=
      fourierInv_eq_phase_integral _ _
    _ = (∫ t : ℝ, complexSeed w hw t * phase t (-2 * Real.pi * x)) ^ 2 :=
      correlation_phase_integral_eq_square w hw _
    _ = (wave w hw x) ^ 2 := by
      rw [← fourierInv_eq_phase_integral, ← wave_eq_fourierInv_seed]

end HVRCompactCorrelationFourierSquare
