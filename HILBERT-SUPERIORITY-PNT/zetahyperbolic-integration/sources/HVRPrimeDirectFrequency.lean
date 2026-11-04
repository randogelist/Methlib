import HVRPrimeLaplaceFrequencyConditional
import Mathlib.MeasureTheory.Integral.ExpDecay

/-!
Direct one-variable integrability route for the actual damped prime density.
The proposed proof uses the global logarithmic-density bound and exponential
majorants, with measurability established explicitly. No theorem in this file
has been locally compiled or externally audited. Transitive reachability of
the targeted integral swap must be checked in the external diagnostic.
-/

noncomputable section
open Filter MeasureTheory
open HVRPrimeLogDensity HVRPrimeDensityFubiniBridge
open HVRPrimeDensityLaplace HVRZetaHyperbolicFrequencyBounds

namespace HVRPrimeDirectFrequency

theorem dampedError_integrable_direct (a : ℝ) (ha : 0 < a) :
    IntegrableOn (dampedError a) (Set.Ioi 0) := by
  have hlog : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hdecay : IntegrableOn (fun u : ℝ => Real.exp (-a * u)) (Set.Ioi 0) :=
    exp_neg_integrableOn_Ioi 0 ha
  have hmajor : IntegrableOn
      (fun u : ℝ => (1 + Real.log 4) * Real.exp (-a * u)) (Set.Ioi 0) :=
    hdecay.const_mul (1 + Real.log 4)
  have hdensity : Measurable logPrimeDensity := by
    unfold logPrimeDensity HVRMonotoneNormalization.normalizedMass
    exact (Real.continuous_exp.comp continuous_neg).measurable.mul
      logPrimeMass_monotone.measurable
  have hexp : Continuous (fun u : ℝ => Complex.exp (-(a : ℂ) * (u : ℂ))) := by
    fun_prop
  have hmeas : AEStronglyMeasurable (dampedError a) (volume.restrict (Set.Ioi (0 : ℝ))) := by
    unfold dampedError
    exact (((Complex.continuous_ofReal.measurable.comp hdensity).sub measurable_const).mul
      hexp.measurable).aestronglyMeasurable
  apply Integrable.mono' hmajor hmeas
  filter_upwards [] with u
  have hρ : ‖(logPrimeDensity u : ℂ) - 1‖ ≤ 1 + Real.log 4 := by
    have h := norm_sub_le (logPrimeDensity u : ℂ) (1 : ℂ)
    simp only [Complex.norm_real, Real.norm_eq_abs, norm_one,
      abs_of_nonneg (logPrimeDensity_nonneg u)] at h
    linarith [logPrimeDensity_le_log_four u]
  have hexpnorm : ‖Complex.exp (-(a : ℂ) * (u : ℂ))‖ = Real.exp (-a * u) := by
    rw [Complex.norm_exp]
    simp [Complex.mul_re]
  calc
    ‖dampedError a u‖ = ‖(logPrimeDensity u : ℂ) - 1‖ * Real.exp (-a * u) := by
      rw [dampedError, norm_mul, hexpnorm]
    _ ≤ (1 + Real.log 4) * Real.exp (-a * u) :=
      mul_le_mul_of_nonneg_right hρ (le_of_lt (Real.exp_pos _))

/-- Mode integrability follows from the direct damped bound and unit phase. -/
theorem damped_phase_integrable_direct (a t : ℝ) (ha : 0 < a) :
    IntegrableOn (fun u : ℝ => dampedError a u * phase t u) (Set.Ioi 0) := by
  have hdamped := dampedError_integrable_direct a ha
  have hphase : Continuous (fun u : ℝ => phase t u) := by
    unfold phase
    fun_prop
  have hmeas : AEStronglyMeasurable (fun u : ℝ => dampedError a u * phase t u)
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    hdamped.aestronglyMeasurable.mul hphase.measurable.aestronglyMeasurable
  apply Integrable.mono' hdamped.norm hmeas
  filter_upwards [] with u
  have hp : ‖phase t u‖ = 1 := by
    simp [phase, Complex.norm_exp, Complex.mul_re, Complex.mul_im]
  simp only [norm_mul, hp, mul_one, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _), le_refl]

theorem first_moment_integrable_direct (a : ℝ) (ha : 0 < a) :
    IntegrableOn (fun u : ℝ => |u| * ‖dampedError a u‖) (Set.Ioi 0) volume := by
  have hhalf : 0 < a / 2 := by linarith
  have hdamped : IntegrableOn (dampedError a) (Set.Ioi 0) volume :=
    dampedError_integrable_direct a ha
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


/-- First-moment frequency Lipschitz bound using the direct one-variable route. -/
theorem primeDensity_frequency_lipschitz_direct (a t r : ℝ) (ha : 0 < a) :
    ‖primeDensityLaplace ((a : ℂ) + (t : ℂ) * Complex.I) -
      primeDensityLaplace ((a : ℂ) + (r : ℂ) * Complex.I)‖ ≤
      |t - r| * ∫ u : ℝ in Set.Ioi 0, |u| * ‖dampedError a u‖ := by
  exact HVRPrimeLaplaceFrequencyConditional.frequency_lipschitz_of_integrable_modes_moment
    a t r (damped_phase_integrable_direct a t ha) (damped_phase_integrable_direct a r ha)
    (first_moment_integrable_direct a ha)

end HVRPrimeDirectFrequency
