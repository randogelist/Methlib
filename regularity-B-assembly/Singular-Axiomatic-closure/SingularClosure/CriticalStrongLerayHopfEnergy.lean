import SingularClosure.CriticalCubeL2
import SingularClosure.CriticalLerayHopf
import SingularClosure.CriticalSerrinTime
import SingularClosure.CriticalSmoothEnergy

/-! The physical rough initial representative and the energy properties of
the constructed strong flow. Positive times retain the literal smooth field. -/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory Filter
open scoped Topology Interval ENNReal ContDiff

namespace SingularClosure
noncomputable section

def CriticalRegularSolution.lerayVelocity
    {ν : ℝ} {a : CriticalSobolev 1} (U : CriticalRegularSolution ν a) : Velocity :=
  fun t => if 0 < t then U.flow.velocity t else (criticalInitialPhysicalL2 a : Field)

def CriticalRegularSolution.lerayGradient
    {ν : ℝ} {a : CriticalSobolev 1} (U : CriticalRegularSolution ν a) :
    ℝ → Vec → (Vec →L[ℝ] Vec) :=
  fun t => if 0 < t then fderiv ℝ (U.flow.velocity t) else 0

theorem CriticalRegularSolution.lerayVelocity_of_pos
    {ν : ℝ} {a : CriticalSobolev 1} (U : CriticalRegularSolution ν a)
    {t : ℝ} (ht : 0 < t) : U.lerayVelocity t = U.flow.velocity t := by
  simp only [CriticalRegularSolution.lerayVelocity, if_pos ht]

theorem CriticalRegularSolution.lerayGradient_of_pos
    {ν : ℝ} {a : CriticalSobolev 1} (U : CriticalRegularSolution ν a)
    {t : ℝ} (ht : 0 < t) : U.lerayGradient t = fderiv ℝ (U.flow.velocity t) := by
  simp only [CriticalRegularSolution.lerayGradient, if_pos ht]

theorem CriticalRegularSolution.lerayVelocity_zero
    {ν : ℝ} {a : CriticalSobolev 1} (U : CriticalRegularSolution ν a) :
    U.lerayVelocity 0 = (criticalInitialPhysicalL2 a : Field) := by
  simp only [CriticalRegularSolution.lerayVelocity, lt_self_iff_false, if_false]

theorem CriticalRegularSolution.lerayVelocity_memLp
    {ν : ℝ} {a : CriticalSobolev 1} (U : CriticalRegularSolution ν a) (t : ℝ) :
    MemLp (U.lerayVelocity t) 2 (volume.restrict unitCube) := by
  by_cases ht : 0 < t
  · rw [U.lerayVelocity_of_pos ht]
    exact critical_continuous_memLp_cube _ (U.flow.velocity_smoothSigmaZero t ht).smooth.continuous 2
  · simp only [CriticalRegularSolution.lerayVelocity, if_neg ht]
    exact Lp.memLp _

private theorem critical_lerayL2Representative_norm_sq (v : Field)
    (hv : MemLp v 2 (volume.restrict unitCube)) :
    ‖criticalL2Representative v‖ ^ 2 = physicalEnergy v := by
  rw [criticalL2Representative_eq v hv, ← real_inner_self_eq_norm_sq,
    L2.inner_def, physicalEnergy_eq_integral_norm_sq]
  apply integral_congr_ae
  filter_upwards [hv.coeFn_toLp] with x hx
  rw [hx, real_inner_self_eq_norm_sq]

private theorem critical_lerayL2Representative_inner (v φ : Field)
    (hv : MemLp v 2 (volume.restrict unitCube))
    (hφ : MemLp φ 2 (volume.restrict unitCube)) :
    inner ℝ (criticalL2Representative v) (hφ.toLp φ) = physicalFieldInner v φ := by
  rw [criticalL2Representative_eq v hv, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hv.coeFn_toLp, hφ.coeFn_toLp] with x hx hφx
  rw [hx, hφx]

theorem CriticalRegularSolution.lerayL2_eq_physicalL2
    {ν : ℝ} {a : CriticalSobolev 1} (U : CriticalRegularSolution ν a)
    (t : ℝ) (ht : 0 ≤ t) :
    criticalL2Representative (U.lerayVelocity t) = U.physicalL2 t := by
  by_cases hp : 0 < t
  · rw [U.lerayVelocity_of_pos hp, U.physicalL2_eq_field t hp]
    exact criticalL2Representative_eq _ (critical_continuous_memLp_cube _
      (U.flow.velocity_smoothSigmaZero t hp).smooth.continuous 2)
  · have hz : t = 0 := le_antisymm (le_of_not_gt hp) ht
    subst t
    rw [U.lerayVelocity_zero, criticalL2Representative_eq _ (Lp.memLp _), Lp.toLp_coeFn]
    simp only [CriticalRegularSolution.physicalL2, U.initial, criticalInitialPhysicalL2]

theorem CriticalRegularSolution.lerayEnergy_eq_norm_sq
    {ν : ℝ} {a : CriticalSobolev 1} (U : CriticalRegularSolution ν a)
    (t : ℝ) (ht : 0 ≤ t) :
    physicalEnergy (U.lerayVelocity t) = ‖U.physicalL2 t‖ ^ 2 := by
  rw [← U.lerayL2_eq_physicalL2 t ht]
  exact (critical_lerayL2Representative_norm_sq _ (U.lerayVelocity_memLp t)).symm

theorem CriticalRegularSolution.lerayL2_continuous
    {ν : ℝ} {a : CriticalSobolev 1} (U : CriticalRegularSolution ν a) :
    ContinuousOn (fun t => criticalL2Representative (U.lerayVelocity t)) (Ici (0 : ℝ)) :=
  U.physicalL2_continuous.congr (fun t ht => U.lerayL2_eq_physicalL2 t ht)

theorem CriticalRegularSolution.leray_weak_continuity
    {ν : ℝ} {a : CriticalSobolev 1} (U : CriticalRegularSolution ν a)
    (φ : Field) (hφ : MemLp φ 2 (volume.restrict unitCube)) :
    ContinuousOn (fun t => physicalFieldInner (U.lerayVelocity t) φ) (Ici (0 : ℝ)) := by
  apply (U.lerayL2_continuous.inner (continuousOn_const (c := hφ.toLp φ))).congr
  intro t _
  exact (critical_lerayL2Representative_inner _ φ (U.lerayVelocity_memLp t) hφ).symm

theorem CriticalRegularSolution.leray_strong_trace
    {ν : ℝ} {a : CriticalSobolev 1} (U : CriticalRegularSolution ν a) :
    Tendsto (fun t => eLpNorm
      (U.lerayVelocity t - (criticalInitialPhysicalL2 a : Field)) 2 (volume.restrict unitCube))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  apply U.physical_eLpNorm_initial_trace.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [U.lerayVelocity_of_pos ht]

theorem CriticalRegularSolution.leray_velocity_energy_class
    {ν : ℝ} {a : CriticalSobolev 1} (U : CriticalRegularSolution ν a)
    (T : ℝ) :
    MemLp (fun t => criticalL2Representative (U.lerayVelocity t)) ⊤
      (volume.restrict (Ioc (0 : ℝ) T)) := by
  have hc := U.lerayL2_continuous.mono (show Icc (0 : ℝ) T ⊆ Ici 0 from fun _ ht => ht.1)
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  have hmem : MemLp (fun t => criticalL2Representative (U.lerayVelocity t)) ⊤
      (volume.restrict (Icc (0 : ℝ) T)) := by
    apply MemLp.of_bound
      (hc.aestronglyMeasurable_of_isCompact isCompact_Icc measurableSet_Icc) C
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact hC t ht
  exact hmem.mono_measure (Measure.restrict_mono_set volume Ioc_subset_Icc_self)

theorem CriticalRegularSolution.leray_spatial_H1
    {ν : ℝ} {a : CriticalSobolev 1} (U : CriticalRegularSolution ν a) (T : ℝ) :
    ∀ᵐ t ∂volume.restrict (Ioc (0 : ℝ) T),
      CriticalPhysicalH1 (U.lerayVelocity t) (U.lerayGradient t) := by
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  rw [U.lerayVelocity_of_pos ht.1, U.lerayGradient_of_pos ht.1]
  exact critical_smooth_physicalH1 _ (U.flow.velocity_smoothSigmaZero t ht.1).smooth
    (U.flow.velocity_smoothSigmaZero t ht.1).periodic

theorem CriticalRegularSolution.lerayGradient_energy_of_pos
    {ν : ℝ} {a : CriticalSobolev 1} (U : CriticalRegularSolution ν a)
    (t : ℝ) (ht : 0 < t) :
    criticalGradientEnergy (U.lerayGradient t) = physicalDissipation (U.flow.velocity t) := by
  rw [U.lerayGradient_of_pos ht]
  exact criticalGradientEnergy_fderiv _ (U.flow.velocity_smoothSigmaZero t ht).smooth

theorem CriticalRegularSolution.leray_dissipation_integrable
    {ν : ℝ} {a : CriticalSobolev 1} (U : CriticalRegularSolution ν a)
    (T : ℝ) (hT : 0 ≤ T)
    (hQ : IntegrableOn (fun t => physicalDissipation (U.flow.velocity t) ^ 2)
      (Icc (0 : ℝ) T) volume) :
    IntervalIntegrable (fun t => criticalGradientEnergy (U.lerayGradient t)) volume 0 T := by
  have hD0 (t : ℝ) : 0 ≤ physicalDissipation (U.flow.velocity t) :=
    integral_nonneg (gradientSquareDensity_nonneg _)
  have hDm : AEStronglyMeasurable (fun t => physicalDissipation (U.flow.velocity t))
      (volume.restrict (Icc (0 : ℝ) T)) := by
    apply (Real.continuous_sqrt.comp_aestronglyMeasurable hQ.aestronglyMeasurable).congr
    exact Filter.Eventually.of_forall (fun t => Real.sqrt_sq (hD0 t))
  have hD2 : MemLp (fun t => physicalDissipation (U.flow.velocity t)) 2
      (volume.restrict (Icc (0 : ℝ) T)) :=
    (memLp_two_iff_integrable_sq hDm).mpr hQ
  have hD1 := hD2.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le hT).mpr
  apply hD1.congr
  filter_upwards [critical_ae_positive_on_Icc T] with t ht
  exact (U.lerayGradient_energy_of_pos t ht).symm

theorem CriticalRegularSolution.leray_gradient_energy_class_of_measurable
    {ν : ℝ} {a : CriticalSobolev 1} (U : CriticalRegularSolution ν a)
    (T : ℝ) (hT : 0 ≤ T)
    (hQ : IntegrableOn (fun t => physicalDissipation (U.flow.velocity t) ^ 2)
      (Icc (0 : ℝ) T) volume)
    (hG : AEStronglyMeasurable
      (fun t => criticalL2Representative (fderiv ℝ (U.flow.velocity t)))
      (volume.restrict (Ioc (0 : ℝ) T))) :
    MemLp (fun t => criticalL2Representative (U.lerayGradient t)) 2
      (volume.restrict (Ioc (0 : ℝ) T)) := by
  have hm : AEStronglyMeasurable
      (fun t => criticalL2Representative (U.lerayGradient t))
      (volume.restrict (Ioc (0 : ℝ) T)) := by
    apply hG.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [U.lerayGradient_of_pos ht.1]
  have hD : IntegrableOn (fun t => criticalGradientEnergy (U.lerayGradient t))
      (Ioc (0 : ℝ) T) volume := (U.leray_dissipation_integrable T hT hQ).1
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  apply (hD.const_mul 3).mono' (hm.norm.pow 2)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  change ‖(‖criticalL2Representative (U.lerayGradient t)‖ ^ 2 : ℝ)‖ ≤ _
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  have hg : MemLp (U.lerayGradient t) 2 (volume.restrict unitCube) := by
    rw [U.lerayGradient_of_pos ht.1]
    exact critical_continuous_memLp_cube _
      ((U.flow.velocity_smoothSigmaZero t ht.1).smooth.continuous_fderiv (by simp)) 2
  rw [criticalL2Representative_eq _ hg, Lp.norm_toLp]
  exact critical_gradient_L2_toReal_sq_le (U.lerayGradient t) hg

private theorem critical_leray_flow_test {ν : ℝ} (L : CriticalPositiveSobolevFlow ν) :
    CriticalPositiveSolenoidalTest L.velocity :=
  ⟨L.velocity_spacetime_smooth, fun t ht => (L.velocity_smoothSigmaZero t ht).periodic,
    fun t ht => (L.velocity_smoothSigmaZero t ht).divergence_free⟩

private theorem critical_leray_flow_pressure_smooth {ν : ℝ}
    (L : CriticalPositiveSobolevFlow ν) (t : ℝ) (ht : 0 < t) :
    ContDiff ℝ ∞ (L.pressure t) := by
  rw [← contDiffOn_univ]
  exact L.pressure_spacetime_smooth.comp
    (contDiff_const.prodMk contDiff_id).contDiffOn (fun x _ => ht)

theorem CriticalRegularSolution.lerayEnergy_hasDerivAt
    {ν : ℝ} {a : CriticalSobolev 1} (U : CriticalRegularSolution ν a)
    (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun r => ‖U.physicalL2 r‖ ^ 2)
      ((-2 * ν) * criticalGradientEnergy (U.lerayGradient t)) t := by
  have h := CRITICAL_SMOOTH_NSE_ENERGY_HAS_DERIV ν U.flow.velocity U.flow.pressure
    (critical_leray_flow_test U.flow) (critical_leray_flow_pressure_smooth U.flow)
    (fun r hr => (CRITICAL_POSITIVE_PHYSICAL_NSE U.flow).pressure_periodic r hr)
    U.flow.physical_equation t ht
  rw [← U.lerayGradient_energy_of_pos t ht] at h
  apply h.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ht] with r hr
  rw [U.physicalL2_eq_field r hr, physicalFieldL2_norm_sq]

/-- Exact energy equality from the rough initial endpoint. -/
theorem CriticalRegularSolution.leray_energy_initial_eq
    {ν : ℝ} {a : CriticalSobolev 1} (U : CriticalRegularSolution ν a)
    (T : ℝ) (hT : 0 ≤ T)
    (hQ : IntegrableOn (fun t => physicalDissipation (U.flow.velocity t) ^ 2)
      (Icc (0 : ℝ) T) volume) :
    physicalEnergy (U.lerayVelocity T) +
      2 * ν * (∫ t in (0 : ℝ)..T, criticalGradientEnergy (U.lerayGradient t)) =
        ‖criticalInitialPhysicalL2 a‖ ^ 2 := by
  have hD := U.leray_dissipation_integrable T hT hQ
  have hcont : ContinuousOn (fun t => ‖U.physicalL2 t‖ ^ 2) (Icc (0 : ℝ) T) :=
    (U.physicalL2_continuous.norm.pow 2).mono (fun t ht => ht.1)
  have hderiv : ∀ t ∈ Ioo (0 : ℝ) T, HasDerivAt (fun r => ‖U.physicalL2 r‖ ^ 2)
      ((-2 * ν) * criticalGradientEnergy (U.lerayGradient t)) t :=
    fun t ht => U.lerayEnergy_hasDerivAt t ht.1
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT hcont hderiv
    (hD.const_mul (-2 * ν))
  rw [intervalIntegral.integral_const_mul] at h
  have hzero : U.physicalL2 0 = criticalInitialPhysicalL2 a := by
    simp only [CriticalRegularSolution.physicalL2, U.initial, criticalInitialPhysicalL2]
  rw [hzero] at h
  rw [U.lerayEnergy_eq_norm_sq T hT]
  linarith

/-- Equality on positive-time intervals follows directly from the same actual
derivative and scalar fundamental theorem of calculus. -/
theorem CriticalRegularSolution.leray_energy_interval_eq
    {ν : ℝ} {a : CriticalSobolev 1} (U : CriticalRegularSolution ν a)
    (T : ℝ) (hT : 0 ≤ T)
    (hQ : IntegrableOn (fun t => physicalDissipation (U.flow.velocity t) ^ 2)
      (Icc (0 : ℝ) T) volume)
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) (htT : t ≤ T) :
    physicalEnergy (U.lerayVelocity t) +
      2 * ν * (∫ r in s..t, criticalGradientEnergy (U.lerayGradient r)) =
        physicalEnergy (U.lerayVelocity s) := by
  have ht : 0 ≤ t := hs.trans hst
  have hD := (U.leray_dissipation_integrable T hT hQ).mono_set
    (show uIcc s t ⊆ uIcc (0 : ℝ) T by
      rw [uIcc_of_le hst, uIcc_of_le hT]
      exact Icc_subset_Icc hs htT)
  have hcont : ContinuousOn (fun r => ‖U.physicalL2 r‖ ^ 2) (Icc s t) :=
    (U.physicalL2_continuous.norm.pow 2).mono (fun r hr => hs.trans hr.1)
  have hd : ∀ r ∈ Ioo s t, HasDerivAt (fun q => ‖U.physicalL2 q‖ ^ 2)
      ((-2 * ν) * criticalGradientEnergy (U.lerayGradient r)) r :=
    fun r hr => U.lerayEnergy_hasDerivAt r (hs.trans_lt hr.1)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hst hcont hd
    (hD.const_mul (-2 * ν))
  rw [intervalIntegral.integral_const_mul] at h
  rw [U.lerayEnergy_eq_norm_sq t ht, U.lerayEnergy_eq_norm_sq s hs]
  linarith

end
end SingularClosure
