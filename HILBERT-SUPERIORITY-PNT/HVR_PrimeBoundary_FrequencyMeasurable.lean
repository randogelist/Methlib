import HVR_PrimeBoundary_AbelLimitConditional
import HVR_PrimeDensity_FubiniIntegrable

noncomputable section
open MeasureTheory HVRPrimeDensityFubiniBridge HVRPrimeDensityFubiniIntegrable
open HVRPrimeBoundaryAbelLimitConditional

/-!
Candidate measurability of the actual frequency-side integrand, obtained from
product integrability and integration of measurable sections. This does not
claim compact support, concentration, or PNT. No local Lean run was performed.
-/
namespace HVRPrimeBoundaryFrequencyMeasurable

/-- For an integrable test and positive damping, the frequency integrand is
almost everywhere strongly measurable; no separate measurability assumption
on the Laplace transform is needed. -/
theorem frequencyIntegrand_aestronglyMeasurable
    (ψ : ℝ → ℂ) (a x : ℝ) (hψ : Integrable ψ volume) (ha : 0 < a) :
    AEStronglyMeasurable (frequencyIntegrand ψ x a) volume := by
  have hpair := (mixed_integrable ψ a x hψ ha).swap
  have hmeas := hpair.aestronglyMeasurable.integral_prod_right'
  change AEStronglyMeasurable
    (fun t : ℝ => ∫ u : ℝ in Set.Ioi 0, mixed ψ a x u t) volume at hmeas
  have heq : (fun t : ℝ => ∫ u : ℝ in Set.Ioi 0, mixed ψ a x u t) =
      frequencyIntegrand ψ x a := by
    funext t
    simp_rw [mixed_factorization]
    rw [integral_const_mul]
    rfl
  rw [heq] at hmeas
  exact hmeas

end HVRPrimeBoundaryFrequencyMeasurable
