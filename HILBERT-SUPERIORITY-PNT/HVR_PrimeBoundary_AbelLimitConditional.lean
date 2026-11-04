import HVR_PrimeDensity_BoundaryLimit
import HVR_PrimeBoundary_OrdinaryFrequencyDecay
import Mathlib.MeasureTheory.Integral.Bochner.Basic

noncomputable section
open Filter MeasureTheory ENNReal
open scoped Topology
open HVRCorrectionBoundaryLimit HVRPrimeDensityLaplace
open HVRPrimeDensityBoundaryLimit HVRPrimeBoundaryOrdinaryFrequencyDecay
open HVRSmoothingBoundaryExtension

/-! A candidate Abel-to-boundary frequency integral limit along the audited
positive reciprocal sequence. Pointwise convergence is discharged using the
actual prime-density Laplace boundary theorem. Measurability and an explicit
integrable majorant remain hypotheses. This is not yet an undamped convolution
identity or a proof of PNT. No Lean was run locally. -/
namespace HVRPrimeBoundaryAbelLimitConditional

def frequencyIntegrand (ψ : ℝ → ℂ) (x a t : ℝ) : ℂ :=
  (ψ t * Complex.exp ((t : ℂ) * Complex.I * (x : ℂ))) *
    primeDensityLaplace ((a : ℂ) + (t : ℂ) * Complex.I)

/-- Conditional frequency-side Abel limit. The explicit uniform domination and
measurability assumptions are not discharged by this lemma. -/
theorem frequency_integral_tendsto_boundary_of_dominated
    (ψ : ℝ → ℂ) (x C : ℝ) (hψ : Integrable ψ volume)
    (hmeas : ∀ n : ℕ, AEStronglyMeasurable
      (frequencyIntegrand ψ x (boundaryEps n)) volume)
    (hdom : ∀ n : ℕ, ∀ᵐ t : ℝ ∂volume,
      ‖frequencyIntegrand ψ x (boundaryEps n) t‖ ≤ C * ‖ψ t‖) :
    Tendsto (fun n : ℕ => ∫ t : ℝ, frequencyIntegrand ψ x (boundaryEps n) t)
      atTop (𝓝 (ordinaryBoundary ψ x)) := by
  have hmajor : Integrable (fun t : ℝ => C * ‖ψ t‖) volume :=
    hψ.norm.const_mul C
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
  unfold ordinaryBoundary
  refine tendsto_integral_of_L1 _
    (aestronglyMeasurable_of_tendsto_ae _ hmeas hlim)
    (Filter.Eventually.of_forall (fun n => hmajor.mono' (hmeas n) (hdom n))) ?_
  simpa only [ofReal_norm] using
    (tendsto_lintegral_norm_of_dominated_convergence hmeas hmajor.hasFiniteIntegral hdom hlim)

end HVRPrimeBoundaryAbelLimitConditional
