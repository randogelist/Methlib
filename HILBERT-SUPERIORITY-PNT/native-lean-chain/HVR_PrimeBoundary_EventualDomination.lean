import HVR_PrimeBoundary_AbelLimitConditional
import Mathlib.Analysis.Normed.Group.Bounded

noncomputable section
open Filter MeasureTheory
open scoped Topology
open HVRCorrectionBoundaryLimit HVRPrimeDensityLaplace
open HVRPrimeDensityBoundaryLimit HVRPrimeBoundaryAbelLimitConditional
open HVRSmoothingBoundaryExtension

/-!
Candidate use of compact-uniform boundary convergence to obtain an eventual
frequency-side bound. No local Lean was run. This does not yet discharge the
all-n domination or measurability hypotheses of the existing Abel glue.
-/
namespace HVRPrimeBoundaryEventualDomination

/-- On each compact frequency set the actual Laplace values have a common
bound for all sufficiently small reciprocal damping parameters. -/
theorem laplace_eventually_bounded_on_compact (K : Set ℝ) (hK : IsCompact K) :
    ∃ C : ℝ, ∀ᶠ n : ℕ in atTop, ∀ t ∈ K,
      ‖primeDensityLaplace ((boundaryEps n : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C := by
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn
    patchedShift_continuous_boundary.continuousOn
  obtain ⟨δ, hδ, huniform⟩ := primeDensityLaplace_uniform_on_compact K hK 1 (by norm_num)
  have heps : ∀ᶠ n : ℕ in atTop, boundaryEps n < δ :=
    boundaryEps_tendsto.eventually (Iio_mem_nhds hδ)
  refine ⟨B + 1, ?_⟩
  filter_upwards [heps] with n hn t ht
  have hnear : ‖primeDensityLaplace ((boundaryEps n : ℂ) + (t : ℂ) * Complex.I) -
      patchedShift ((t : ℂ) * Complex.I)‖ < 1 := by
    simpa only [dist_eq_norm] using
      huniform (boundaryEps n) t (boundaryEps_pos n) hn ht
  have htriangle : ‖primeDensityLaplace ((boundaryEps n : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      ‖primeDensityLaplace ((boundaryEps n : ℂ) + (t : ℂ) * Complex.I) -
        patchedShift ((t : ℂ) * Complex.I)‖ +
      ‖patchedShift ((t : ℂ) * Complex.I)‖ := by
    calc
      ‖primeDensityLaplace ((boundaryEps n : ℂ) + (t : ℂ) * Complex.I)‖ =
          ‖(primeDensityLaplace ((boundaryEps n : ℂ) + (t : ℂ) * Complex.I) -
            patchedShift ((t : ℂ) * Complex.I)) + patchedShift ((t : ℂ) * Complex.I)‖ := by
        simp only [sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
  linarith [hB t ht]

/-- A common eventual domination for the actual frequency integrand follows
when the frequency test vanishes outside the chosen compact set. -/
theorem frequency_eventually_dominated_on_compact
    (ψ : ℝ → ℂ) (x : ℝ) (K : Set ℝ) (hK : IsCompact K)
    (hsupport : ∀ t : ℝ, ψ t ≠ 0 → t ∈ K) :
    ∃ C : ℝ, ∀ᶠ n : ℕ in atTop, ∀ t : ℝ,
      ‖frequencyIntegrand ψ x (boundaryEps n) t‖ ≤ C * ‖ψ t‖ := by
  obtain ⟨C, hC⟩ := laplace_eventually_bounded_on_compact K hK
  refine ⟨C, ?_⟩
  filter_upwards [hC] with n hn t
  by_cases ht : ψ t = 0
  · simp only [frequencyIntegrand, ht, zero_mul, norm_zero, mul_zero, le_refl]
  · have hnormexp : ‖Complex.exp ((t : ℂ) * Complex.I * (x : ℂ))‖ = 1 := by
      rw [Complex.norm_exp]
      simp [Complex.mul_re, Complex.mul_im]
    have hbound := hn t (hsupport t ht)
    have hmul := mul_le_mul_of_nonneg_left hbound (norm_nonneg (ψ t))
    simp only [frequencyIntegrand, norm_mul, hnormexp, mul_one]
    nlinarith

end HVRPrimeBoundaryEventualDomination
