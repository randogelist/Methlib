import HVR_PrimeBoundary_EventualDomination
import HVR_PrimeDensity_SpatialAbel
import HVR_PrimeDensity_FubiniIntegrable

noncomputable section
open Filter MeasureTheory
open scoped Topology
open HVRCorrectionBoundaryLimit HVRPrimeDensityLaplace
open HVRPrimeDensityBoundaryLimit HVRPrimeBoundaryAbelLimitConditional
open HVRPrimeBoundaryOrdinaryFrequencyDecay HVRPrimeBoundaryEventualDomination
open HVRPrimeDensityFubiniBridge HVRPrimeDensityFubiniIntegrable
open HVRPrimeDensitySpatialAbel HVRSmoothingBoundaryExtension

/-!
Candidate improvement of the conditional Abel glue: compact frequency
support supplies the eventual domination automatically, using the filter form
of dominated convergence. Measurability of the frequency integrands and L1
integrability of the inverse kernel remain explicit. Not locally compiled.
-/
namespace HVRPrimeBoundaryEventualAbelGlue

/-- Compact support removes the common domination hypothesis. -/
theorem frequency_integral_tendsto_boundary_of_compact_support
    (ψ : ℝ → ℂ) (x : ℝ) (K : Set ℝ) (hK : IsCompact K)
    (hsupport : ∀ t : ℝ, ψ t ≠ 0 → t ∈ K)
    (hψ : Integrable ψ volume)
    (hmeas : ∀ n : ℕ, AEStronglyMeasurable
      (frequencyIntegrand ψ x (boundaryEps n)) volume) :
    Tendsto (fun n : ℕ => ∫ t : ℝ, frequencyIntegrand ψ x (boundaryEps n) t)
      atTop (𝓝 (ordinaryBoundary ψ x)) := by
  obtain ⟨C, hC⟩ := frequency_eventually_dominated_on_compact ψ x K hK hsupport
  have hmajor : Integrable (fun t : ℝ => C * ‖ψ t‖) volume := hψ.norm.const_mul C
  have hlim : ∀ᵐ t : ℝ ∂volume,
      Tendsto (fun n : ℕ => frequencyIntegrand ψ x (boundaryEps n) t)
        atTop (𝓝 ((ψ t * Complex.exp ((t : ℂ) * Complex.I * (x : ℂ))) *
          patchedShift ((t : ℂ) * Complex.I))) := by
    filter_upwards [] with t
    have hcst : Tendsto (fun _ : ℕ =>
        ψ t * Complex.exp ((t : ℂ) * Complex.I * (x : ℂ))) atTop
        (𝓝 (ψ t * Complex.exp ((t : ℂ) * Complex.I * (x : ℂ)))) :=
      tendsto_const_nhds
    have h := hcst.mul (primeDensityLaplace_boundaryEps_tendsto t)
    simpa only [frequencyIntegrand] using h
  have hmeas' : ∀ᶠ n : ℕ in atTop, AEStronglyMeasurable
      (frequencyIntegrand ψ x (boundaryEps n)) volume := Filter.Eventually.of_forall hmeas
  have hdom : ∀ᶠ n : ℕ in atTop, ∀ᵐ t : ℝ ∂volume,
      ‖frequencyIntegrand ψ x (boundaryEps n) t‖ ≤ C * ‖ψ t‖ := by
    filter_upwards [hC] with n hn
    exact Filter.Eventually.of_forall hn
  have hc := tendsto_integral_filter_of_dominated_convergence
    (fun t : ℝ => C * ‖ψ t‖) hmeas' hdom hmajor hlim
  simpa only [ordinaryBoundary] using hc

/-- The undamped actual prime-error convolution is the boundary integral;
measurability and integrability of the inverse kernel are still hypotheses. -/
theorem undamped_eq_ordinaryBoundary_of_compact_support
    (ψ : ℝ → ℂ) (x : ℝ) (K : Set ℝ) (hK : IsCompact K)
    (hsupport : ∀ t : ℝ, ψ t ≠ 0 → t ∈ K)
    (hψ : Integrable ψ volume) (hkernel : Integrable (kernel ψ) volume)
    (hmeas : ∀ n : ℕ, AEStronglyMeasurable
      (frequencyIntegrand ψ x (boundaryEps n)) volume) :
    undamped (kernel ψ) x = ordinaryBoundary ψ x := by
  have hs := spatial_abel_tendsto (kernel ψ) hkernel x
  have hf := frequency_integral_tendsto_boundary_of_compact_support
    ψ x K hK hsupport hψ hmeas
  have heq : ∀ n : ℕ,
      (∫ u : ℝ in Set.Ioi 0,
        dampedError (boundaryEps n) u * kernel ψ (x - u)) =
      (∫ t : ℝ, frequencyIntegrand ψ x (boundaryEps n) t) := by
    intro n
    simpa only [frequencyIntegrand] using
      abel_smoothing_eq_frequency_integral_of_integrable ψ (boundaryEps n) x hψ
        (boundaryEps_pos n)
  have hf' : Tendsto (fun n : ℕ => ∫ u : ℝ in Set.Ioi 0,
      dampedError (boundaryEps n) u * kernel ψ (x - u)) atTop
      (𝓝 (ordinaryBoundary ψ x)) := by
    apply hf.congr'
    filter_upwards [] with n
    exact (heq n).symm
  exact tendsto_nhds_unique hs hf'

end HVRPrimeBoundaryEventualAbelGlue
