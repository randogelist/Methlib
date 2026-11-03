import HVR_PrimeDensity_BoundaryLimit
import NativeDominatedLimit
import Mathlib.Analysis.Normed.Group.Bounded

/-!
Compact-uniform boundary convergence for the actual prime-density Laplace
transform, tested against an integrable frequency weight supported in a
compact set. The proof uses one-variable norm estimates for integrals and
pre-existing compact-uniform convergence, without a direct call to dominated
convergence. It keeps the original separate measurability premise. The
upstream analytic and transitive Mathlib dependencies require inspection.
This is an uncompiled candidate pending external cached Lean and named audit.
-/
noncomputable section
open Filter MeasureTheory
open scoped Topology
open HVRCorrectionBoundaryLimit HVRPrimeDensityLaplace
open HVRPrimeDensityBoundaryLimit HVRSmoothingBoundaryExtension

namespace HVRCompactBoundaryLimit

def frequencyIntegrand (ψ : ℝ → ℂ) (x a t : ℝ) : ℂ :=
  (ψ t * Complex.exp ((t : ℂ) * Complex.I * (x : ℂ))) *
    primeDensityLaplace ((a : ℂ) + (t : ℂ) * Complex.I)

def boundaryIntegrand (ψ : ℝ → ℂ) (x t : ℝ) : ℂ :=
  (ψ t * Complex.exp ((t : ℂ) * Complex.I * (x : ℂ))) *
    patchedShift ((t : ℂ) * Complex.I)

/-- Norm of the ordinary exponential frequency factor. -/
theorem norm_frequency_phase (t x : ℝ) :
    ‖Complex.exp ((t : ℂ) * Complex.I * (x : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  simp [Complex.mul_re, Complex.mul_im]

/-- Compact-uniform convergence gives the original PNT-specific frequency
integral limit with the same integrable-weight and measurability premises. -/
theorem frequency_integral_tendsto_boundary
    (ψ : ℝ → ℂ) (x : ℝ) (K : Set ℝ) (hK : IsCompact K)
    (hψ : Integrable ψ volume)
    (hsupport : ∀ t : ℝ, ψ t ≠ 0 → t ∈ K)
    (hmeas : ∀ n : ℕ, AEStronglyMeasurable
      (frequencyIntegrand ψ x (boundaryEps n)) volume) :
    Tendsto (fun n : ℕ => ∫ t : ℝ, frequencyIntegrand ψ x (boundaryEps n) t)
      atTop (𝓝 (∫ t : ℝ, boundaryIntegrand ψ x t)) := by
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
  refine Metric.tendsto_nhds.mpr fun ε hε => ?_
  let W : ℝ := ∫ t : ℝ, ‖ψ t‖
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
  obtain ⟨δ, hδ, huniform⟩ := primeDensityLaplace_uniform_on_compact K hK η hη
  have heps : ∀ᶠ n : ℕ in atTop, boundaryEps n < δ :=
    boundaryEps_tendsto.eventually (Iio_mem_nhds hδ)
  filter_upwards [heps] with n hn
  have hnear (t : ℝ) (ht : t ∈ K) :
      ‖primeDensityLaplace ((boundaryEps n : ℂ) + (t : ℂ) * Complex.I) -
        patchedShift ((t : ℂ) * Complex.I)‖ < η := by
    simpa only [dist_eq_norm] using
      huniform (boundaryEps n) t (boundaryEps_pos n) hn ht
  have hmajorF : Integrable (fun t : ℝ => (|B| + η + 1) * ‖ψ t‖) volume :=
    hw.const_mul (|B| + η + 1)
  have hf : Integrable (frequencyIntegrand ψ x (boundaryEps n)) volume := by
    apply hmajorF.mono' (hmeas n)
    filter_upwards [] with t
    by_cases ht : ψ t = 0
    · simp [frequencyIntegrand, ht]
    · have htK := hsupport t ht
      have hBt := hB t htK
      have htri : ‖primeDensityLaplace ((boundaryEps n : ℂ) + (t : ℂ) * Complex.I)‖ ≤
          ‖primeDensityLaplace ((boundaryEps n : ℂ) + (t : ℂ) * Complex.I) -
            patchedShift ((t : ℂ) * Complex.I)‖ +
          ‖patchedShift ((t : ℂ) * Complex.I)‖ := by
        calc
          ‖primeDensityLaplace ((boundaryEps n : ℂ) + (t : ℂ) * Complex.I)‖ =
              ‖(primeDensityLaplace ((boundaryEps n : ℂ) + (t : ℂ) * Complex.I) -
                patchedShift ((t : ℂ) * Complex.I)) +
                patchedShift ((t : ℂ) * Complex.I)‖ := by simp
          _ ≤ _ := norm_add_le _ _
      have hF : ‖primeDensityLaplace ((boundaryEps n : ℂ) + (t : ℂ) * Complex.I)‖ ≤
          |B| + η + 1 := by linarith [hnear t htK, le_abs_self B]
      have hm := mul_le_mul_of_nonneg_left hF (norm_nonneg (ψ t))
      simp only [frequencyIntegrand, norm_mul, norm_frequency_phase, mul_one]
      nlinarith
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
  have herror := HVRNativeDominatedLimit.integral_error_le_weighted η hf hg hw hbound
  have hfinal : ‖(∫ t : ℝ, frequencyIntegrand ψ x (boundaryEps n) t) -
      (∫ t : ℝ, boundaryIntegrand ψ x t)‖ < ε :=
    lt_of_le_of_lt herror hsmall
  simpa only [dist_eq_norm] using hfinal

end HVRCompactBoundaryLimit
