import SingularClosure.CriticalPhysicalQuantitative
import SingularClosure.CriticalRegularityContracts
import SingularClosure.CriticalSmoothEnergyNorm
import SingularClosure.CriticalGradientEnergyBound
import SingularClosure.CriticalSpatialNormMeasurable

/-! The actual spatial L6 norm belongs to time L4. The integrability follows
from physical gradient energy and the inherited kinetic-energy bound. -/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory Filter
open scoped Topology Interval ENNReal ContDiff

namespace SingularClosure
noncomputable section

theorem critical_smooth_physicalH1 (v : Field)
    (hv : ContDiff ℝ ∞ v) (hp : SpatialPeriodic v) :
    CriticalPhysicalH1 v (fderiv ℝ v) := by
  refine ⟨critical_continuous_memLp_cube v hv.continuous 2,
    critical_continuous_memLp_cube _ (hv.continuous_fderiv (by simp)) 2, ?_⟩
  refine ⟨fun _ : ℕ => v, fun _ => hv, fun _ => hp, ?_, ?_⟩ <;>
    simpa only [sub_self, eLpNorm_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0))

/-- Uniform physical kinetic energy of an actual critical regular solution. -/
theorem CriticalRegularSolution.physicalEnergy_le
    {ν : ℝ} {a : CriticalSobolev 1} (U : CriticalRegularSolution ν a)
    (t : ℝ) (ht : 0 < t) : physicalEnergy (U.flow.velocity t) ≤ ‖a‖ ^ 2 := by
  let w : CriticalSobolev 0 := criticalSobolevLower 0 1 (by norm_num) (U.critical t)
  have hw : criticalCoeff 0 w = (U.flow.state 0 t).val := by
    rw [criticalSobolevLower_coeff, U.coefficient_agreement t ht]
  have heq := critical_smoothFourierSynthesis_energy_eq_norm_sq
    (U.flow.state 0 t).val
    (ALL_SOBOLEV_IMP_RAPID_SCALAR _ (U.flow.state_all_mem t ht))
    (U.flow.reality t ht) w hw
  change physicalEnergy (U.flow.velocity t) = ‖w‖ ^ 2 at heq
  rw [heq]
  apply pow_le_pow_left₀ (norm_nonneg _) _ 2
  exact (criticalSobolevLower_norm_le 0 1 (by norm_num) (U.critical t)).trans
    (U.critical_bound t ht.le)

theorem CRITICAL_SMOOTH_L6_FOURTH_BOUND :
    ∃ K : ℝ, 0 < K ∧ ∀ v : Field, ContDiff ℝ ∞ v → SpatialPeriodic v →
      criticalSpatialNorm 6 v ^ 4 ≤
        K * (9 * physicalDissipation v ^ 2 + physicalEnergy v ^ 2) := by
  obtain ⟨L, hL, hSob⟩ := CRITICAL_PHYSICAL_H1_L6_REAL
  refine ⟨8 * L ^ 4, by positivity, ?_⟩
  intro v hv hp
  have hH := critical_smooth_physicalH1 v hv hp
  have h6 := hSob v (fderiv ℝ v) hH
  have hD0 := criticalSpatialNorm_nonneg 2 (fderiv ℝ v)
  have hW0 := criticalSpatialNorm_nonneg 2 v
  have hD2 : criticalSpatialNorm 2 (fderiv ℝ v) ^ 2 ≤ 3 * physicalDissipation v := by
    simpa only [criticalSpatialNorm, criticalGradientEnergy_fderiv v hv] using
      critical_gradient_L2_toReal_sq_le (fderiv ℝ v) hH.derivative_L2
  have hW2 : criticalSpatialNorm 2 v ^ 2 = physicalEnergy v :=
    critical_velocity_L2_toReal_sq_eq_physicalEnergy v hH.velocity_L2
  have hD4 : criticalSpatialNorm 2 (fderiv ℝ v) ^ 4 ≤ 9 * physicalDissipation v ^ 2 := by
    calc
      _ = (criticalSpatialNorm 2 (fderiv ℝ v) ^ 2) ^ 2 := by ring
      _ ≤ (3 * physicalDissipation v) ^ 2 := pow_le_pow_left₀ (sq_nonneg _) hD2 2
      _ = _ := by ring
  have hW4 : criticalSpatialNorm 2 v ^ 4 = physicalEnergy v ^ 2 := by
    rw [show criticalSpatialNorm 2 v ^ 4 = (criticalSpatialNorm 2 v ^ 2) ^ 2 by ring, hW2]
  have hadd : (criticalSpatialNorm 2 (fderiv ℝ v) + criticalSpatialNorm 2 v) ^ 4 ≤
      8 * (criticalSpatialNorm 2 (fderiv ℝ v) ^ 4 + criticalSpatialNorm 2 v ^ 4) := by
    simpa using add_pow_le hD0 hW0 4
  calc
    _ ≤ (L * (criticalSpatialNorm 2 (fderiv ℝ v) + criticalSpatialNorm 2 v)) ^ 4 :=
      pow_le_pow_left₀ (criticalSpatialNorm_nonneg 6 v) h6 4
    _ = L ^ 4 * (criticalSpatialNorm 2 (fderiv ℝ v) + criticalSpatialNorm 2 v) ^ 4 := mul_pow _ _ _
    _ ≤ L ^ 4 * (8 *
        (criticalSpatialNorm 2 (fderiv ℝ v) ^ 4 + criticalSpatialNorm 2 v ^ 4)) :=
      mul_le_mul_of_nonneg_left hadd (pow_nonneg hL.le 4)
    _ = (8 * L ^ 4) *
        (criticalSpatialNorm 2 (fderiv ℝ v) ^ 4 + criticalSpatialNorm 2 v ^ 4) := by ring
    _ ≤ (8 * L ^ 4) * (9 * physicalDissipation v ^ 2 + physicalEnergy v ^ 2) :=
      mul_le_mul_of_nonneg_left (add_le_add hD4 hW4.le) (by positivity)

/-- This is the concrete Serrin hypothesis required by weak-strong uniqueness. -/
theorem CriticalRegularSolution.serrin_time_memLp
    {ν : ℝ} {a : CriticalSobolev 1} (U : CriticalRegularSolution ν a)
    (T : ℝ)
    (hquartic : IntegrableOn (fun t => physicalDissipation (U.flow.velocity t) ^ 2)
      (Icc (0 : ℝ) T) volume) :
    MemLp (fun t => criticalSpatialNorm 6 (U.flow.velocity t)) 4
      (volume.restrict (Ioc (0 : ℝ) T)) := by
  let μ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) T)
  have hmeas : AEStronglyMeasurable
      (fun t => criticalSpatialNorm 6 (U.flow.velocity t)) μ :=
    criticalPositive_spatialNorm_six_aestronglyMeasurable U.flow T
  obtain ⟨K, hK, hbound⟩ := CRITICAL_SMOOTH_L6_FOURTH_BOUND
  have hQ : Integrable (fun t => physicalDissipation (U.flow.velocity t) ^ 2) μ :=
    hquartic.mono_set Ioc_subset_Icc_self
  have hdom : Integrable (fun t => K *
      (9 * physicalDissipation (U.flow.velocity t) ^ 2 + ‖a‖ ^ 4)) μ :=
    ((hQ.const_mul 9).add (integrable_const _)).const_mul K
  have hfour : Integrable (fun t => criticalSpatialNorm 6 (U.flow.velocity t) ^ 4) μ := by
    apply hdom.mono' (hmeas.pow 4)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [Real.norm_of_nonneg (pow_nonneg (criticalSpatialNorm_nonneg 6 _) 4)]
    have hE := U.physicalEnergy_le t ht.1
    have hE0 : 0 ≤ physicalEnergy (U.flow.velocity t) := by
      rw [physicalEnergy_eq_integral_norm_sq]
      exact integral_nonneg (fun x => sq_nonneg _)
    have hE2 : physicalEnergy (U.flow.velocity t) ^ 2 ≤ ‖a‖ ^ 4 := by
      simpa only [← pow_mul] using pow_le_pow_left₀ hE0 hE 2
    exact (hbound _ (U.flow.velocity_smoothSigmaZero t ht.1).smooth
      (U.flow.velocity_smoothSigmaZero t ht.1).periodic).trans
      (mul_le_mul_of_nonneg_left (add_le_add le_rfl hE2) hK.le)
  apply (integrable_norm_rpow_iff hmeas
    (by norm_num : (4 : ℝ≥0∞) ≠ 0) (by norm_num : (4 : ℝ≥0∞) ≠ ∞)).mp
  simpa only [ENNReal.toReal_ofNat, Real.rpow_natCast, Real.norm_eq_abs,
    show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs] using hfour

end
end SingularClosure
