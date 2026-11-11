import SingularClosure.CriticalSerrinTime

/-! A homogeneous physical L6 estimate for the actual mean-zero smooth flow.
The norm contraction supplies Poincare directly from the Fourier realization. -/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory Filter
open scoped Topology Interval ENNReal ContDiff

namespace SingularClosure
noncomputable section

theorem CriticalPositiveSobolevFlow.physicalEnergy_le_dissipation
    {ν : ℝ} (L : CriticalPositiveSobolevFlow ν) (t : ℝ) (ht : 0 < t) :
    physicalEnergy (L.velocity t) ≤ physicalDissipation (L.velocity t) := by
  let c : FourierCoeff := (L.state 0 t).val
  let w : CriticalSobolev 2 := criticalSobolevOfCoeff 2 c
    (critical_order_two_mem_of_torus_one c (L.state_all_mem t ht 1))
  have hw : criticalCoeff 2 w = c := criticalSobolevOfCoeff_coeff _ _ _
  let w0 : CriticalSobolev 0 := criticalSobolevLower 0 2 (by norm_num) w
  have hw0 : criticalCoeff 0 w0 = c := by rw [criticalSobolevLower_coeff, hw]
  have hrapid : ∀ i : Fin 3, RapidScalarFourier (fun k => c k i) :=
    ALL_SOBOLEV_IMP_RAPID_SCALAR c (L.state_all_mem t ht)
  have hE := critical_smoothFourierSynthesis_energy_eq_norm_sq c hrapid (L.reality t ht) w0 hw0
  have hD := critical_smoothFourierSynthesis_dissipation_eq_norm_sq c hrapid
    (L.reality t ht) (L.mean_zero t ht) w hw
  change physicalEnergy (L.velocity t) = ‖w0‖ ^ 2 at hE
  change physicalDissipation (L.velocity t) = ‖w‖ ^ 2 at hD
  rw [hE, hD]
  exact pow_le_pow_left₀ (norm_nonneg _) (criticalSobolevLower_norm_le 0 2 (by norm_num) w) 2

theorem CRITICAL_POSITIVE_HOMOGENEOUS_L6_FOURTH :
    ∃ K : ℝ, 0 < K ∧ ∀ (ν : ℝ) (L : CriticalPositiveSobolevFlow ν)
      (t : ℝ), 0 < t →
        criticalSpatialNorm 6 (L.velocity t) ^ 4 ≤ K * physicalDissipation (L.velocity t) ^ 2 := by
  obtain ⟨K, hK, hb⟩ := CRITICAL_SMOOTH_L6_FOURTH_BOUND
  refine ⟨10 * K, by positivity, ?_⟩
  intro ν L t ht
  have hE := L.physicalEnergy_le_dissipation t ht
  have hE0 : 0 ≤ physicalEnergy (L.velocity t) := by
    rw [physicalEnergy_eq_integral_norm_sq]
    exact integral_nonneg (fun x => sq_nonneg _)
  have hE2 := pow_le_pow_left₀ hE0 hE 2
  calc
    _ ≤ K * (9 * physicalDissipation (L.velocity t) ^ 2 + physicalEnergy (L.velocity t) ^ 2) :=
      hb _ (L.velocity_smoothSigmaZero t ht).smooth (L.velocity_smoothSigmaZero t ht).periodic
    _ ≤ K * (9 * physicalDissipation (L.velocity t) ^ 2 + physicalDissipation (L.velocity t) ^ 2) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl hE2) hK.le
    _ = _ := by ring

def criticalPhysicalL6FourthConstant : ℝ := CRITICAL_POSITIVE_HOMOGENEOUS_L6_FOURTH.choose

theorem criticalPhysicalL6FourthConstant_pos : 0 < criticalPhysicalL6FourthConstant :=
  CRITICAL_POSITIVE_HOMOGENEOUS_L6_FOURTH.choose_spec.1

theorem criticalPhysicalL6FourthConstant_bound
    {ν : ℝ} (L : CriticalPositiveSobolevFlow ν) (t : ℝ) (ht : 0 < t) :
    criticalSpatialNorm 6 (L.velocity t) ^ 4 ≤
      criticalPhysicalL6FourthConstant * physicalDissipation (L.velocity t) ^ 2 :=
  CRITICAL_POSITIVE_HOMOGENEOUS_L6_FOURTH.choose_spec.2 ν L t ht

theorem CriticalRegularSolution.serrin_fourth_integral_le
    {ν : ℝ} {a : CriticalSobolev 1} (U : CriticalRegularSolution ν a)
    (T : ℝ) (hT : 0 ≤ T)
    (hquartic : IntegrableOn (fun t => physicalDissipation (U.flow.velocity t) ^ 2)
      (Icc (0 : ℝ) T) volume) :
    (∫ t in (0 : ℝ)..T, criticalSpatialNorm 6 (U.flow.velocity t) ^ 4) ≤
      criticalPhysicalL6FourthConstant *
        (∫ t in (0 : ℝ)..T, physicalDissipation (U.flow.velocity t) ^ 2) := by
  have h6 := U.serrin_time_memLp T hquartic
  have h6int : IntegrableOn (fun t => criticalSpatialNorm 6 (U.flow.velocity t) ^ 4)
      (Ioc (0 : ℝ) T) volume := by
    have h := h6.integrable_norm_pow (by norm_num : (4 : ℕ) ≠ 0)
    simpa only [Real.norm_eq_abs, show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs] using h
  have hDint : IntegrableOn (fun t => physicalDissipation (U.flow.velocity t) ^ 2)
      (Ioc (0 : ℝ) T) volume := hquartic.mono_set Ioc_subset_Icc_self
  rw [intervalIntegral.integral_of_le hT, intervalIntegral.integral_of_le hT,
    ← integral_const_mul]
  apply integral_mono_ae h6int (hDint.const_mul _)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact criticalPhysicalL6FourthConstant_bound U.flow t ht.1

end
end SingularClosure
