import HVRZetaHyperbolicFiniteFrequency
import Mathlib.MeasureTheory.Integral.ExpDecay

/-!
Candidate first absolute moment of the actual damped prime error.

The proof uses the established global logarithmic-prime-density bound and an
elementary exponential majorant. It does not invoke the Fubini swap by name.
The complete transitive proof dependency graph must still be inspected.

Candidate only: no local Lean execution or external theorem audit.
-/

noncomputable section
open Filter MeasureTheory
open HVRPrimeLogDensity HVRPrimeDensityFubiniBridge

namespace HVRPrimeWeightedMoment

/-- The absolute first moment needed by the phase discretization is finite. -/
theorem dampedError_first_moment_integrable (a : ℝ) (ha : 0 < a) :
    IntegrableOn (fun u : ℝ => |u| * ‖dampedError a u‖) (Set.Ioi 0) volume := by
  have hhalf : 0 < a / 2 := by linarith
  have hdamped : IntegrableOn (dampedError a) (Set.Ioi 0) volume := by
    have h := HVRZetaHyperbolicFiniteFrequency.actual_fixed_frequency_integrable
      (fun _ : ℝ => (1 : ℂ)) a 0 0 ha
    simpa [mixed] using h
  have hdecay : IntegrableOn (fun u : ℝ => Real.exp (-(a / 2) * u))
      (Set.Ioi 0) volume := exp_neg_integrableOn_Ioi 0 hhalf
  have hmajor : IntegrableOn
      (fun u : ℝ => ((a / 2)⁻¹ * (1 + Real.log 4)) *
        Real.exp (-(a / 2) * u)) (Set.Ioi 0) volume :=
    hdecay.const_mul ((a / 2)⁻¹ * (1 + Real.log 4))
  have hmeas : AEStronglyMeasurable
      (fun u : ℝ => |u| * ‖dampedError a u‖)
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    (continuous_id.abs.measurable.aestronglyMeasurable).mul
      hdamped.aestronglyMeasurable.norm
  apply Integrable.mono' hmajor hmeas
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu0 : 0 ≤ u := le_of_lt hu
  have hlog : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hρ : ‖(logPrimeDensity u : ℂ) - 1‖ ≤ 1 + Real.log 4 := by
    have h := norm_sub_le (logPrimeDensity u : ℂ) (1 : ℂ)
    simp only [Complex.norm_real, Real.norm_eq_abs, norm_one,
      abs_of_nonneg (logPrimeDensity_nonneg u)] at h
    linarith [logPrimeDensity_le_log_four u]
  have hexpnorm : ‖Complex.exp (-(a : ℂ) * (u : ℂ))‖ =
      Real.exp (-a * u) := by
    rw [Complex.norm_exp]
    simp [Complex.mul_re]
  have hfbound : ‖dampedError a u‖ ≤
      (1 + Real.log 4) * Real.exp (-a * u) := by
    unfold dampedError
    rw [norm_mul, hexpnorm]
    exact mul_le_mul_of_nonneg_right hρ (le_of_lt (Real.exp_pos _))
  have hpow : u ≤ (a / 2)⁻¹ * Real.exp ((a / 2) * u) :=
    Real.le_inv_mul_exp u hhalf
  have hexp :
      Real.exp ((a / 2) * u) * Real.exp (-a * u) =
        Real.exp (-(a / 2) * u) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    ‖|u| * ‖dampedError a u‖‖ = u * ‖dampedError a u‖ := by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (norm_nonneg _)),
        abs_of_nonneg hu0]
    _ ≤ u * ((1 + Real.log 4) * Real.exp (-a * u)) :=
      mul_le_mul_of_nonneg_left hfbound hu0
    _ ≤ ((a / 2)⁻¹ * Real.exp ((a / 2) * u)) *
          ((1 + Real.log 4) * Real.exp (-a * u)) := by
      apply mul_le_mul_of_nonneg_right hpow
      exact mul_nonneg (by linarith) (le_of_lt (Real.exp_pos _))
    _ = ((a / 2)⁻¹ * (1 + Real.log 4)) *
          Real.exp (-(a / 2) * u) := by rw [← hexp]; ring

end HVRPrimeWeightedMoment

