import HVRCompactCorrelationQuadrature
import HVRFrequencyMeshLimit

/-! Candidate direct finite-cell approximation to the Fourier integral of
the actual compact seed. This module does not use a continuous integral
swap or the Fourier convolution theorem. External compilation, axiom audit,
and dependency tracing remain pending. -/

noncomputable section
open Filter MeasureTheory
open HVRPhysicalKernelCandidate HVRZetaHyperbolicFrequencyBounds
open HVRFrequencyIntervalCells HVRFrequencyWeightedCoefficients
open HVRPrimeLeftQuadrature HVRCompactCorrelationQuadrature
open scoped BigOperators Topology

namespace HVRCompactSeedPhaseGrid

/-- Cell-integral coefficients paired with sampled Fourier phases. -/
def sampledPhase (w : ℝ) (hw : 0 < w) (N : ℕ) (x : ℝ) : ℂ :=
  ∑ i ∈ Finset.range N,
    (∫ t : ℝ in gridCell (w / 2) N i, complexSeed w hw t) *
      phase (gridPoint (w / 2) N i) x

/-- The cell-weighted samples converge to the whole-line seed transform. -/
theorem sampledPhase_tendsto (w : ℝ) (hw : 0 < w) (x : ℝ) :
    Tendsto (fun N : ℕ => sampledPhase w hw N x) atTop
      (𝓝 (∫ t : ℝ, complexSeed w hw t * phase t x)) := by
  have hR : 0 ≤ w / 2 := by positivity
  have hψ : Integrable (complexSeed w hw) :=
    (complexSeed_smooth w hw).continuous.integrable_of_hasCompactSupport
      (complexSeed_compact w hw)
  have hweight : ∀ t : ℝ, weightedFrequency (complexSeed w hw) 0 t =
      complexSeed w hw t := by
    intro t
    simp [weightedFrequency]
  have hfull : intervalKernel (w / 2) (complexSeed w hw) 0 x =
      ∫ t : ℝ, complexSeed w hw t * phase t x := by
    unfold intervalKernel
    simp_rw [hweight]
    apply setIntegral_eq_integral_of_ae_compl_eq_zero
    filter_upwards [] with t ht
    rw [complexSeed_zero_off_interval w hw t ht, zero_mul]
  have hsample : ∀ N : ℕ, sampleKernel (w / 2) N (complexSeed w hw) 0 x =
      sampledPhase w hw N x := by
    intro N
    unfold sampleKernel sampledPhase
    simp_rw [hweight, integral_mul_const]
  apply HVRFrequencyMeshLimit.tendsto_of_grid_error (w / 2)
    (|x| * ∫ t : ℝ, ‖complexSeed w hw t‖)
  intro N hN
  have h := intervalKernel_sample_error (w / 2) N (complexSeed w hw) 0 x
    hR hN hψ
  rw [hfull, hsample N, norm_sub_rev] at h
  simpa only [mul_assoc] using h

end HVRCompactSeedPhaseGrid
