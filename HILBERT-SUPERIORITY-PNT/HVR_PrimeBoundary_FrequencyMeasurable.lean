import HVR_PrimeBoundary_AbelLimitConditional
import HVRPrimeDirectFrequency

noncomputable section
open MeasureTheory HVRPrimeDensityFubiniBridge HVRPrimeDensityLaplace
open HVRPrimeBoundaryAbelLimitConditional

/-! Frequency-side measurability obtained from the direct one-variable
first-moment Lipschitz estimate. The imported direct estimate has an external
standard-axiom audit; this replacement still requires its own build, audit,
and dependency trace. It does not prove the integral-swap replacement. -/
namespace HVRPrimeBoundaryFrequencyMeasurable

/-- Positive damping gives continuity in the frequency variable. -/
theorem primeDensity_frequency_continuous_native (a : ℝ) (ha : 0 < a) :
    Continuous (fun t : ℝ => primeDensityLaplace ((a : ℂ) + (t : ℂ) * Complex.I)) := by
  let M : ℝ := ∫ u : ℝ in Set.Ioi 0, |u| * ‖dampedError a u‖
  have hM : 0 ≤ M := by
    dsimp [M]
    exact integral_nonneg (fun u => mul_nonneg (abs_nonneg u) (norm_nonneg _))
  let K : NNReal := ⟨M, hM⟩
  have hL : LipschitzWith K
      (fun t : ℝ => primeDensityLaplace ((a : ℂ) + (t : ℂ) * Complex.I)) := by
    apply LipschitzWith.of_dist_le_mul
    intro t r
    change dist (primeDensityLaplace ((a : ℂ) + (t : ℂ) * Complex.I))
      (primeDensityLaplace ((a : ℂ) + (r : ℂ) * Complex.I)) ≤ M * dist t r
    simpa [dist_eq_norm, Real.norm_eq_abs, M, mul_comm] using
      HVRPrimeDirectFrequency.primeDensity_frequency_lipschitz_direct a t r ha
  exact hL.continuous

/-- The frequency integrand is measurable without product-section integration. -/
theorem frequencyIntegrand_aestronglyMeasurable
    (ψ : ℝ → ℂ) (a x : ℝ) (hψ : Integrable ψ volume) (ha : 0 < a) :
    AEStronglyMeasurable (frequencyIntegrand ψ x a) volume := by
  have hexp : Continuous (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I * (x : ℂ))) := by
    fun_prop
  have hweight : AEStronglyMeasurable
      (fun t : ℝ => ψ t * Complex.exp ((t : ℂ) * Complex.I * (x : ℂ))) volume :=
    hψ.aestronglyMeasurable.mul hexp.measurable.aestronglyMeasurable
  have htransform : AEStronglyMeasurable
      (fun t : ℝ => primeDensityLaplace ((a : ℂ) + (t : ℂ) * Complex.I)) volume :=
    (primeDensity_frequency_continuous_native a ha).measurable.aestronglyMeasurable
  exact hweight.mul htransform

end HVRPrimeBoundaryFrequencyMeasurable
