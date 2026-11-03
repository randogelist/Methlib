import HVR_PrimeLogDensity
import Mathlib.MeasureTheory.Integral.Bochner.Basic

noncomputable section
open MeasureTheory
open HVRPrimeLogDensity HVRMonotoneNormalization

/-! Candidate measurability and weighted-integrability estimates for the
actual prime density. These lemmas do not construct a smoothing kernel or
establish a Fourier or PNT limit. No local Lean run was performed. -/
namespace HVRPrimeDensityWeightedIntegrability

/-- The actual normalized prime count is measurable, even though it jumps. -/
theorem logPrimeDensity_measurable : Measurable logPrimeDensity := by
  unfold logPrimeDensity normalizedMass
  have hexp : Continuous (fun t : ℝ => Real.exp (-t)) := by fun_prop
  exact hexp.measurable.mul logPrimeMass_monotone.measurable

/-- Integrable kernel weights remain integrable after multiplication by the
bounded actual density at a measurable shifted argument. -/
theorem weighted_density_integrableOn
    (k q : ℝ → ℝ) (S : Set ℝ) (hk : IntegrableOn k S volume)
    (hq : Measurable q) :
    IntegrableOn (fun v : ℝ => k v * logPrimeDensity (q v)) S volume := by
  have hmajor : IntegrableOn (fun v : ℝ => Real.log 4 * ‖k v‖) S volume :=
    hk.norm.const_mul (Real.log 4)
  have hd : Measurable (fun v : ℝ => logPrimeDensity (q v)) :=
    logPrimeDensity_measurable.comp hq
  have hmeas : AEStronglyMeasurable (fun v : ℝ => k v * logPrimeDensity (q v))
      (volume.restrict S) := hk.aestronglyMeasurable.mul hd.aestronglyMeasurable
  apply Integrable.mono' hmajor hmeas
  apply Filter.Eventually.of_forall
  intro v
  have hn : 0 ≤ logPrimeDensity (q v) := logPrimeDensity_nonneg (q v)
  have hnorm : ‖logPrimeDensity (q v)‖ = logPrimeDensity (q v) := by
    rw [Real.norm_eq_abs, abs_of_nonneg hn]
  calc
    ‖k v * logPrimeDensity (q v)‖ = ‖k v‖ * logPrimeDensity (q v) := by
      rw [norm_mul, hnorm]
    _ ≤ ‖k v‖ * Real.log 4 :=
      mul_le_mul_of_nonneg_left (logPrimeDensity_le_log_four (q v)) (norm_nonneg _)
    _ = Real.log 4 * ‖k v‖ := mul_comm _ _

end HVRPrimeDensityWeightedIntegrability
