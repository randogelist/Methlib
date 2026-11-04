import HVRZetaHyperbolicFrequencyBounds
import HVRPrimeWeightedMoment

/-!
Candidate actual prime-density Laplace frequency Lipschitz bound.

This composes the finite-frequency adapter with the abstract phase estimate and
the candidate first-moment bound. It does not establish a finite partition or
the two quadrature convergence premises, and its transitive dependencies have
not been traced. No local Lean run or matching audit has been performed.
-/

noncomputable section
open MeasureTheory
open HVRPrimeDensityFubiniBridge HVRPrimeDensityLaplace
open HVRZetaHyperbolicFiniteFrequency HVRZetaHyperbolicFrequencyBounds
open HVRPrimeWeightedMoment

namespace HVRPrimeLaplaceFrequencyBounds

/-- The sampled actual mixed term is a damped error times a Fourier phase. -/
theorem actual_mixed_eq_damped_phase (a t u : ℝ) :
    mixed (fun _ : ℝ => (1 : ℂ)) a 0 u t = dampedError a u * phase t u := by
  have hexp : Complex.exp ((t : ℂ) * Complex.I * ((0 - u : ℝ) : ℂ)) =
      Complex.exp (Complex.I * ((-t * u : ℝ) : ℂ)) := by
    congr 1
    push_cast
    ring
  simpa only [mixed, phase, one_mul] using
    congrArg (fun z : ℂ => dampedError a u * z) hexp

/-- Integral representation of the actual prime-density Laplace line. -/
theorem primeDensityLaplace_eq_damped_phase (a t : ℝ) :
    primeDensityLaplace ((a : ℂ) + (t : ℂ) * Complex.I) =
      ∫ u : ℝ in Set.Ioi 0, dampedError a u * phase t u := by
  have h := actual_fixed_frequency (fun _ : ℝ => (1 : ℂ)) a 0 t
  have heq : (fun u : ℝ => mixed (fun _ : ℝ => (1 : ℂ)) a 0 u t) =
      (fun u : ℝ => dampedError a u * phase t u) := by
    funext u
    exact actual_mixed_eq_damped_phase a t u
  rw [heq] at h
  simpa using h.symm

/-- Quantitative frequency bound for the actual prime-density transform. -/
theorem primeDensityLaplace_frequency_lipschitz
    (a t r : ℝ) (ha : 0 < a) :
    ‖primeDensityLaplace ((a : ℂ) + (t : ℂ) * Complex.I) -
      primeDensityLaplace ((a : ℂ) + (r : ℂ) * Complex.I)‖ ≤
      |t - r| *
        ∫ u : ℝ in Set.Ioi 0, |u| * ‖dampedError a u‖ := by
  have hfun (z : ℝ) :
      (fun u : ℝ => mixed (fun _ : ℝ => (1 : ℂ)) a 0 u z) =
        (fun u : ℝ => dampedError a u * phase z u) := by
    funext u
    exact actual_mixed_eq_damped_phase a z u
  have ht := actual_fixed_frequency_integrable
    (fun _ : ℝ => (1 : ℂ)) a 0 t ha
  have hr := actual_fixed_frequency_integrable
    (fun _ : ℝ => (1 : ℂ)) a 0 r ha
  rw [hfun t] at ht
  rw [hfun r] at hr
  rw [primeDensityLaplace_eq_damped_phase a t,
    primeDensityLaplace_eq_damped_phase a r]
  exact integral_phase_frequency_lipschitz
    (μ := volume.restrict (Set.Ioi (0 : ℝ))) (dampedError a) t r ht hr
    (dampedError_first_moment_integrable a ha)

end HVRPrimeLaplaceFrequencyBounds

