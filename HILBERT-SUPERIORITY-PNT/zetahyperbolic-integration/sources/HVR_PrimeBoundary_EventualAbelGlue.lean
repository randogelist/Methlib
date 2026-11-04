import HVR_PrimeBoundary_EventualDomination
import HVR_PrimeDensity_SpatialAbel
import HVR_PrimeDensity_FubiniIntegrable
import HVRPrimeGridSwapDirect
import NativeDominatedLimit

noncomputable section
open Filter MeasureTheory
open scoped Topology
open HVRCorrectionBoundaryLimit HVRPrimeDensityLaplace
open HVRPrimeDensityBoundaryLimit HVRPrimeBoundaryAbelLimitConditional
open HVRPrimeBoundaryOrdinaryFrequencyDecay HVRPrimeBoundaryEventualDomination
open HVRPrimeDensityFubiniBridge HVRPrimeDensityFubiniIntegrable
open HVRPrimeDensitySpatialAbel HVRSmoothingBoundaryExtension

/-! Abel limits on compact frequency support via the uniform boundary estimate
and the one-variable weighted integral error bound. -/
namespace HVRPrimeBoundaryEventualAbelGlue

private def boundaryIntegrand (ψ : ℝ → ℂ) (x t : ℝ) : ℂ :=
  (ψ t * Complex.exp ((t : ℂ) * Complex.I * (x : ℂ))) *
    patchedShift ((t : ℂ) * Complex.I)

/-- Norm of the ordinary exponential frequency factor. -/
private theorem norm_frequency_phase (t x : ℝ) :
    ‖Complex.exp ((t : ℂ) * Complex.I * (x : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  simp [Complex.mul_re, Complex.mul_im]

/-- Eventual weighted-uniform error bounds imply convergence of the integrals. -/
theorem integral_tendsto_of_eventual_weighted_uniform_error
    (F : ℕ → ℝ → ℂ) (G : ℝ → ℂ) (weight : ℝ → ℝ)
    (hG : Integrable G volume) (hw : Integrable weight volume)
    (hW : 0 ≤ ∫ t : ℝ, weight t)
    (hbound : ∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop,
      Integrable (F n) volume ∧ ∀ᵐ t : ℝ ∂volume, ‖F n t - G t‖ ≤ η * weight t) :
    Tendsto (fun n : ℕ => ∫ t : ℝ, F n t) atTop (𝓝 (∫ t : ℝ, G t)) := by
  refine Metric.tendsto_nhds.mpr fun ε hε => ?_
  let W : ℝ := ∫ t : ℝ, weight t
  let η : ℝ := ε / (W + 1)
  have hW' : 0 ≤ W := hW
  have hden : 0 < W + 1 := by linarith
  have hη : 0 < η := by dsimp [η]; exact div_pos hε hden
  have hsmall : η * W < ε := by
    dsimp [η]
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ hden).2
    have hmul : ε * W < ε * (W + 1) :=
      mul_lt_mul_of_pos_left (by linarith : W < W + 1) hε
    nlinarith
  filter_upwards [hbound η hη] with n hn
  have hestimate := HVRNativeDominatedLimit.integral_error_le_weighted η hn.1 hG hw hn.2
  have hfinal : ‖(∫ t : ℝ, F n t) - (∫ t : ℝ, G t)‖ < ε :=
    lt_of_le_of_lt hestimate hsmall
  simpa only [dist_eq_norm] using hfinal

/-- Compact uniform convergence controls the integral error by the L¹ mass of ψ. -/
theorem frequency_integral_tendsto_boundary_of_compact_support
    (ψ : ℝ → ℂ) (x : ℝ) (K : Set ℝ) (hK : IsCompact K)
    (hsupport : ∀ t : ℝ, ψ t ≠ 0 → t ∈ K)
    (hψ : Integrable ψ volume)
    (hmeas : ∀ n : ℕ, AEStronglyMeasurable
      (frequencyIntegrand ψ x (boundaryEps n)) volume) :
    Tendsto (fun n : ℕ => ∫ t : ℝ, frequencyIntegrand ψ x (boundaryEps n) t)
      atTop (𝓝 (ordinaryBoundary ψ x)) := by
  change Tendsto _ atTop (𝓝 (∫ t : ℝ, boundaryIntegrand ψ x t))
  have hw : Integrable (fun t : ℝ => ‖ψ t‖) volume := hψ.norm
  have hW : 0 ≤ ∫ t : ℝ, ‖ψ t‖ := integral_nonneg fun t => norm_nonneg _
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn
    patchedShift_continuous_boundary.continuousOn
  have he : Continuous (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I * (x : ℂ))) := by
    fun_prop
  have hmeasG : AEStronglyMeasurable (boundaryIntegrand ψ x) volume := by
    exact (hψ.aestronglyMeasurable.mul he.aestronglyMeasurable).mul
      patchedShift_continuous_boundary.aestronglyMeasurable
  have hmajorG : Integrable (fun t : ℝ => (|B| + 1) * ‖ψ t‖) volume :=
    hw.const_mul (|B| + 1)
  have hg : Integrable (boundaryIntegrand ψ x) volume := by
    apply hmajorG.mono' hmeasG
    filter_upwards [] with t
    by_cases ht : ψ t = 0
    · simp [boundaryIntegrand, ht]
    · have hBt : ‖patchedShift ((t : ℂ) * Complex.I)‖ ≤ |B| + 1 := by
        have h0 := hB t (hsupport t ht)
        linarith [le_abs_self B]
      have hm := mul_le_mul_of_nonneg_left hBt (norm_nonneg (ψ t))
      simp only [boundaryIntegrand, norm_mul, norm_frequency_phase, mul_one]
      nlinarith
  obtain ⟨C, hdom⟩ := frequency_eventually_dominated_on_compact ψ x K hK hsupport
  have hmajorF : Integrable (fun t : ℝ => C * ‖ψ t‖) volume := hw.const_mul C
  have hf : ∀ᶠ n : ℕ in atTop,
      Integrable (frequencyIntegrand ψ x (boundaryEps n)) volume := by
    filter_upwards [hdom] with n hCn
    exact hmajorF.mono' (hmeas n) (Filter.Eventually.of_forall hCn)
  apply integral_tendsto_of_eventual_weighted_uniform_error
    (fun n => frequencyIntegrand ψ x (boundaryEps n)) (boundaryIntegrand ψ x)
    (fun t => ‖ψ t‖) hg hw hW
  intro η hη
  obtain ⟨δ, hδ, huniform⟩ := primeDensityLaplace_uniform_on_compact K hK η hη
  have heps : ∀ᶠ n : ℕ in atTop, boundaryEps n < δ :=
    boundaryEps_tendsto.eventually (Iio_mem_nhds hδ)
  filter_upwards [heps, hf] with n hn hfn
  have hnear (t : ℝ) (ht : t ∈ K) :
      ‖primeDensityLaplace ((boundaryEps n : ℂ) + (t : ℂ) * Complex.I) -
        patchedShift ((t : ℂ) * Complex.I)‖ < η := by
    simpa only [dist_eq_norm] using
      huniform (boundaryEps n) t (boundaryEps_pos n) hn ht
  have hbound : ∀ᵐ t : ℝ ∂volume,
      ‖frequencyIntegrand ψ x (boundaryEps n) t - boundaryIntegrand ψ x t‖ ≤
        η * ‖ψ t‖ := by
    filter_upwards [] with t
    by_cases ht : ψ t = 0
    · simp [frequencyIntegrand, boundaryIntegrand, ht]
    · have hfactor : frequencyIntegrand ψ x (boundaryEps n) t - boundaryIntegrand ψ x t =
          (ψ t * Complex.exp ((t : ℂ) * Complex.I * (x : ℂ))) *
          (primeDensityLaplace ((boundaryEps n : ℂ) + (t : ℂ) * Complex.I) -
            patchedShift ((t : ℂ) * Complex.I)) := by
        simp only [frequencyIntegrand, boundaryIntegrand]
        ring
      have hm := mul_le_mul_of_nonneg_left (le_of_lt (hnear t (hsupport t ht)))
        (norm_nonneg (ψ t))
      rw [hfactor, norm_mul, norm_mul, norm_frequency_phase, mul_one]
      nlinarith
  exact ⟨hfn, hbound⟩

/-- The undamped actual prime-error convolution is the boundary integral;
measurability and integrability of the inverse kernel are still hypotheses. -/
theorem undamped_eq_ordinaryBoundary_of_compact_support
    (ψ : ℝ → ℂ) (x : ℝ) (K : Set ℝ) (hK : IsCompact K)
    (hsupport : ∀ t : ℝ, ψ t ≠ 0 → t ∈ K)
    (hψ : Integrable ψ volume) (hkernel : Integrable (kernel ψ) volume)
    (hmeas : ∀ n : ℕ, AEStronglyMeasurable
      (frequencyIntegrand ψ x (boundaryEps n)) volume) :
    undamped (kernel ψ) x = ordinaryBoundary ψ x := by
  have hcompact : HasCompactSupport ψ :=
    HasCompactSupport.of_support_subset_isCompact hK (by
      intro t ht
      exact hsupport t ht)
  have hs := spatial_abel_tendsto (kernel ψ) hkernel x
  have hf := frequency_integral_tendsto_boundary_of_compact_support
    ψ x K hK hsupport hψ hmeas
  have heq : ∀ n : ℕ,
      (∫ u : ℝ in Set.Ioi 0,
        dampedError (boundaryEps n) u * kernel ψ (x - u)) =
      (∫ t : ℝ, frequencyIntegrand ψ x (boundaryEps n) t) := by
    intro n
    simpa only [frequencyIntegrand] using
      HVRPrimeGridSwapDirect.abel_smoothing_eq_frequency_integral_of_compact_support
        ψ (boundaryEps n) x (boundaryEps_pos n) hψ hcompact
  have hf' : Tendsto (fun n : ℕ => ∫ u : ℝ in Set.Ioi 0,
      dampedError (boundaryEps n) u * kernel ψ (x - u)) atTop
      (𝓝 (ordinaryBoundary ψ x)) := by
    apply hf.congr'
    filter_upwards [] with n
    exact (heq n).symm
  exact tendsto_nhds_unique hs hf'

end HVRPrimeBoundaryEventualAbelGlue
