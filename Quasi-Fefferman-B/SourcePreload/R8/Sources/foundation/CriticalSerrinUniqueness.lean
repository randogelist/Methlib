import SingularClosure.CriticalRelativeEnergyTransport
import SingularClosure.CriticalRelativeEnergyIntegrable
import SingularClosure.CriticalGradientEnergyBound
import SingularClosure.CriticalSmoothLpContinuity
import SingularClosure.CriticalAdmissibleTimes
import SingularClosure.CriticalLocalUniqueness

/-! Actual physical weak--strong uniqueness.  The relative-energy inequality,
transport bound, admissible initial times and their limiting trace are all
proved from the stated physical NSE and Leray--Hopf hypotheses. -/

set_option autoImplicit false
set_option Elab.async true

open Set Filter MeasureTheory
open scoped BigOperators ContDiff ENNReal Topology Interval

namespace SingularClosure

noncomputable section

theorem critical_physicalEnergy_eq_norm_toLp_sq (v : Field)
    (hv : MemLp v 2 (volume.restrict unitCube)) :
    physicalEnergy v = ‖hv.toLp v‖ ^ 2 := by
  rw [← criticalL2Representative_norm_sq v hv, criticalL2Representative_eq v hv]

theorem critical_physicalEnergy_sub_eq_norm_toLp_sub_sq (v w : Field)
    (hv : MemLp v 2 (volume.restrict unitCube))
    (hw : MemLp w 2 (volume.restrict unitCube)) :
    physicalEnergy (v - w) = ‖hv.toLp v - hw.toLp w‖ ^ 2 := by
  rw [← hv.toLp_sub hw]
  exact critical_physicalEnergy_eq_norm_toLp_sq (v - w) (hv.sub hw)

/-- A genuine Leray--Hopf solution agrees with a positive-time classical
solution sharing its strong physical L2 trace and satisfying the actual
Serrin L4-time/L6-space bound.  Equality is that of physical L2 representatives. -/
theorem CRITICAL_LERAY_HOPF_SERRIN_COMPARISON_ON
    (ν : ℝ) (hν : 0 < ν) (a₀ : CriticalPhysicalL2)
    (v u : Velocity) (G : ℝ → Vec → (Vec →L[ℝ] Vec)) (p : Pressure)
    (hv : CriticalLerayHopf ν a₀ v G)
    (hu : CriticalPositiveSolenoidalTest u)
    (hp : ∀ r : ℝ, 0 < r → ContDiff ℝ ∞ (p r))
    (hpp : ∀ r : ℝ, 0 < r → SpatialPeriodic (p r))
    (hNSE : ∀ r : ℝ, 0 < r → ∀ x : Vec,
      timeDerivative u r x + convection (u r) x + gradient (p r) x =
        ν • laplacian (u r) x)
    (hu_trace : Tendsto
      (fun t => eLpNorm (u t - (a₀ : Vec → Vec)) 2 (volume.restrict unitCube))
      (𝓝[>] (0 : ℝ)) (𝓝 0))
    (T : ℝ) (hT : 0 < T)
    (hSerrin : MemLp (fun t => criticalSpatialNorm 6 (u t)) 4
      (volume.restrict (Ioc (0 : ℝ) T))) :
    ∀ t ∈ Ioc (0 : ℝ) T, v t =ᵐ[volume.restrict unitCube] u t := by
  obtain ⟨C, hC, htransport⟩ := CRITICAL_ROUGH_TRANSPORT_ENERGY_BOUND
  let U : ℝ → ℝ := fun r => criticalSpatialNorm 6 (u r)
  let B : ℝ → ℝ := fun r => 216 * C ^ 4 * (U r) ^ 4 / ν ^ 3 +
    3 * C ^ 2 * (U r) ^ 2 / ν
  let A : ℝ → ℝ := fun r => 2 * B r
  let E : ℝ → ℝ := fun r => physicalEnergy (v r - u r)
  have hUc : ContinuousOn U (Ioc (0 : ℝ) T) :=
    hu.eLpNorm_six_toReal_continuousOn T
  have hBc : ContinuousOn B (Ioc (0 : ℝ) T) :=
    ((continuousOn_const.mul (hUc.pow 4)).div_const (ν ^ 3)).add
      ((continuousOn_const.mul (hUc.pow 2)).div_const ν)
  have hAc : ContinuousOn A (Ioc (0 : ℝ) T) := continuousOn_const.mul hBc
  have hAnonneg : ∀ r ∈ Ioc (0 : ℝ) T, 0 ≤ A r := by
    intro r hr
    dsimp [A, B]
    positivity
  have hEnonneg : ∀ r ∈ Ioc (0 : ℝ) T, 0 ≤ E r := by
    intro r hr
    dsimp [E]
    rw [physicalEnergy_eq_integral_norm_sq]
    exact integral_nonneg (fun x => sq_nonneg _)
  haveI : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) T)) :=
    ⟨by simp only [Measure.restrict_apply_univ, Real.volume_Ioc]; finiteness⟩
  have hBI : IntervalIntegrable B volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le).mpr
      (criticalSerrinEnergyCoefficient_integrable ν C U hSerrin)
  have hAI : IntervalIntegrable A volume 0 T := hBI.const_mul 2
  obtain ⟨ε, hε, hε_zero⟩ := CRITICAL_ADMISSIBLE_TIMES_TENDSTO_ZERO hT
    (fun s => ∀ t ∈ Icc s T, physicalEnergy (v t) +
      2 * ν * (∫ r in s..t, criticalGradientEnergy (G r)) ≤ physicalEnergy (v s))
    (hv.energy_intervals T hT)
  have hεWithin : Tendsto ε atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hε_zero, Eventually.of_forall (fun n => (hε n).1.1)⟩
  have hvε (n : ℕ) : MemLp (v (ε n)) 2 (volume.restrict unitCube) :=
    hv.velocity_L2 (ε n) (hε n).1.1.le
  have huε (n : ℕ) : MemLp (u (ε n)) 2 (volume.restrict unitCube) :=
    critical_continuous_memLp_cube _ (hu.spatial_smooth (hε n).1.1).continuous 2
  have ha₀ : MemLp (a₀ : Vec → Vec) 2 (volume.restrict unitCube) := Lp.memLp a₀
  have hv_trace_L2 := critical_toLp_tendsto_of_eLpNorm_sub
    (fun n => v (ε n)) (a₀ : Vec → Vec) hvε ha₀ (hv.strong_trace.comp hεWithin)
  have hu_trace_L2 := critical_toLp_tendsto_of_eLpNorm_sub
    (fun n => u (ε n)) (a₀ : Vec → Vec) huε ha₀ (hu_trace.comp hεWithin)
  have htrace : Tendsto (fun n => E (ε n)) atTop (𝓝 0) := by
    have heq (n : ℕ) : E (ε n) =
        ‖(hvε n).toLp (v (ε n)) - (huε n).toLp (u (ε n))‖ ^ 2 :=
      critical_physicalEnergy_sub_eq_norm_toLp_sub_sq _ _ (hvε n) (huε n)
    simpa only [heq, sub_self, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] using
      (hv_trace_L2.sub hu_trace_L2).norm.pow 2
  have hprod (n : ℕ) : IntervalIntegrable (fun r => A r * E r) volume (ε n) T :=
    CRITICAL_RELATIVE_ENERGY_PRODUCT_INTERVAL_INTEGRABLE hv hu A (ε n) T
      (hε n).1.1 (hε n).1.2 (hAc.mono (fun r hr =>
        ⟨lt_of_lt_of_le (hε n).1.1 hr.1, hr.2⟩))
  have hrelative : ∀ n t, t ∈ Icc (ε n) T →
      E t ≤ E (ε n) + ∫ r in ε n..t, A r * E r := by
    intro n t ht
    have htpos : 0 < t := lt_of_lt_of_le (hε n).1.1 ht.1
    have hcoefB : ContinuousOn B (Icc (ε n) t) := hBc.mono (fun r hr =>
      ⟨lt_of_lt_of_le (hε n).1.1 hr.1, hr.2.trans ht.2⟩)
    have hBE : IntervalIntegrable (fun r => B r * E r) volume (ε n) t :=
      CRITICAL_RELATIVE_ENERGY_PRODUCT_INTERVAL_INTEGRABLE hv hu B (ε n) t
        (hε n).1.1 ht.1 hcoefB
    obtain ⟨hD, hR, hrel⟩ := CRITICAL_LH_SMOOTH_RELATIVE_ENERGY_TRANSPORT
      ν hν a₀ v u G p hv hu hp hpp hNSE (ε n) t (hε n).1.1 ht.1 ((hε n).2 t ht)
    have hupper : IntervalIntegrable (fun r =>
        (ν / 2) * criticalGradientEnergy (G r - fderiv ℝ (u r)) + B r * E r)
        volume (ε n) t := (hD.const_mul (ν / 2)).add hBE
    have hH1 : ∀ᵐ r ∂volume.restrict (Ioc (ε n) t), CriticalPhysicalH1 (v r) (G r) :=
      ae_restrict_of_ae_restrict_of_subset (Ioc_subset_Ioc (hε n).1.1.le le_rfl)
        (hv.spatial_H1 t htpos)
    have hpoint : (fun r => criticalRoughTransport (v r - u r)
        (G r - fderiv ℝ (u r)) (u r)) ≤ᵐ[volume.restrict (Ioc (ε n) t)]
        (fun r => (ν / 2) * criticalGradientEnergy (G r - fderiv ℝ (u r)) + B r * E r) := by
      filter_upwards [hH1, ae_restrict_mem measurableSet_Ioc] with r hHr hr
      have hrpos : 0 < r := (hε n).1.1.trans hr.1
      have hus := hu.spatial_smooth hrpos
      exact (le_abs_self _).trans (htransport ν hν (u r) (v r - u r)
        (G r - fderiv ℝ (u r)) (critical_continuous_memLp_cube _ hus.continuous 6)
        (hHr.sub_smooth (u r) hus (hu.periodic r hrpos)))
    have hbound : (∫ r in ε n..t, criticalRoughTransport (v r - u r)
        (G r - fderiv ℝ (u r)) (u r)) ≤
        (ν / 2) * (∫ r in ε n..t, criticalGradientEnergy (G r - fderiv ℝ (u r))) +
          (∫ r in ε n..t, B r * E r) := by
      calc
        _ ≤ ∫ r in ε n..t,
            (ν / 2) * criticalGradientEnergy (G r - fderiv ℝ (u r)) + B r * E r := by
          rw [intervalIntegral.integral_of_le ht.1, intervalIntegral.integral_of_le ht.1]
          exact setIntegral_mono_ae_restrict hR.1 hupper.1 hpoint
        _ = _ := by
          rw [intervalIntegral.integral_add (hD.const_mul (ν / 2)) hBE,
            intervalIntegral.integral_const_mul]
    have hDnonneg : 0 ≤ ∫ r in ε n..t,
        criticalGradientEnergy (G r - fderiv ℝ (u r)) :=
      intervalIntegral.integral_nonneg_of_forall ht.1
        (fun r => criticalGradientEnergy_nonneg _)
    have hAint : (∫ r in ε n..t, A r * E r) = 2 * (∫ r in ε n..t, B r * E r) := by
      simp only [A, mul_assoc, intervalIntegral.integral_const_mul]
    change E t + 2 * ν * (∫ r in ε n..t,
      criticalGradientEnergy (G r - fderiv ℝ (u r))) ≤
      E (ε n) + 2 * (∫ r in ε n..t,
        criticalRoughTransport (v r - u r) (G r - fderiv ℝ (u r)) (u r)) at hrel
    rw [hAint]
    nlinarith only [hrel, hbound, mul_nonneg hν.le hDnonneg]
  have hzero := CRITICAL_RELATIVE_ENERGY_ZERO_OF_LOCAL_ADMISSIBLE_TRACE hT
    hEnonneg hAc hAnonneg hAI hprod (le_refl (∫ r in (0 : ℝ)..T, A r))
    (fun n => (hε n).1) hε_zero htrace hrelative
  intro t ht
  have hvL2 := hv.velocity_L2 t ht.1.le
  have huL2 : MemLp (u t) 2 (volume.restrict unitCube) :=
    critical_continuous_memLp_cube _ (hu.spatial_smooth ht.1).continuous 2
  have hd := hvL2.sub huL2
  have hn : ‖hd.toLp (v t - u t)‖ = 0 := by
    have hsq : ‖hd.toLp (v t - u t)‖ ^ 2 = 0 := by
      rw [← critical_physicalEnergy_eq_norm_toLp_sq (v t - u t) hd]
      exact hzero t ht
    nlinarith only [hsq, norm_nonneg (hd.toLp (v t - u t))]
  have hz : hd.toLp (v t - u t) = 0 := norm_eq_zero.mp hn
  have hzae : (v t - u t) =ᵐ[volume.restrict unitCube] (0 : Field) :=
    hd.coeFn_toLp.symm.trans (Lp.eq_zero_iff_ae_eq_zero.mp hz)
  filter_upwards [hzae] with x hx
  exact sub_eq_zero.mp hx

end

end SingularClosure
