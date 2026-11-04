import HVRFrequencyTransformGrid
import HVRPrimeLaplaceFrequencyBounds

/-!
First-moment route to the actual prime-density Laplace frequency bound, with
the two mode-integrability premises and first absolute moment explicit. This
avoids the unconditional upstream moment and mode-integrability proofs; a
transitive dependency trace is required even for this conditional route.
Uncompiled candidate: no Lean was run locally.
-/

noncomputable section
open MeasureTheory
open HVRPrimeDensityFubiniBridge HVRPrimeDensityLaplace
open HVRZetaHyperbolicFrequencyBounds

namespace HVRPrimeLaplaceFrequencyConditional

theorem frequency_lipschitz_of_integrable_modes_moment
    (a t r : ℝ)
    (ht : IntegrableOn (fun u : ℝ => dampedError a u * phase t u) (Set.Ioi 0))
    (hr : IntegrableOn (fun u : ℝ => dampedError a u * phase r u) (Set.Ioi 0))
    (hw : IntegrableOn (fun u : ℝ => |u| * ‖dampedError a u‖) (Set.Ioi 0)) :
    ‖primeDensityLaplace ((a : ℂ) + (t : ℂ) * Complex.I) -
      primeDensityLaplace ((a : ℂ) + (r : ℂ) * Complex.I)‖ ≤
      |t - r| * ∫ u : ℝ in Set.Ioi 0, |u| * ‖dampedError a u‖ := by
  rw [HVRPrimeLaplaceFrequencyBounds.primeDensityLaplace_eq_damped_phase a t,
    HVRPrimeLaplaceFrequencyBounds.primeDensityLaplace_eq_damped_phase a r]
  exact integral_phase_frequency_lipschitz
    (μ := volume.restrict (Set.Ioi (0 : ℝ))) (dampedError a) t r ht hr hw

end HVRPrimeLaplaceFrequencyConditional
