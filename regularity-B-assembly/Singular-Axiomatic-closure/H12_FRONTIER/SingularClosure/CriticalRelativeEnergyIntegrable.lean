import SingularClosure.CriticalLerayHopf
import SingularClosure.CriticalSmoothEnergy

/-! Local integrability of the actual relative energy and its product with
any continuous time coefficient.  All integrability is derived from the
physical Leray--Hopf class and the genuine integrated momentum equation. -/

set_option autoImplicit false
set_option Elab.async true

open Set Filter MeasureTheory
open scoped ContDiff ENNReal Topology Interval

namespace SingularClosure

noncomputable section

theorem criticalL2Representative_norm_sq (v : Field)
    (hv : MemLp v 2 (volume.restrict unitCube)) :
    ‖criticalL2Representative v‖ ^ 2 = physicalEnergy v := by
  rw [criticalL2Representative_eq v hv, ← real_inner_self_eq_norm_sq,
    L2.inner_def, physicalEnergy_eq_integral_norm_sq]
  apply integral_congr_ae
  filter_upwards [hv.coeFn_toLp] with x hx
  rw [hx, real_inner_self_eq_norm_sq]

/-- The standard energy class implies actual time integrability of kinetic
energy on each positive compact time slab. -/
theorem CriticalLerayHopf.physicalEnergy_intervalIntegrable
    {ν : ℝ} {a₀ : CriticalPhysicalL2} {v : Velocity}
    {G : ℝ → Vec → (Vec →L[ℝ] Vec)} (hv : CriticalLerayHopf ν a₀ v G)
    (s t : ℝ) (hs : 0 < s) (hst : s ≤ t) :
    IntervalIntegrable (fun r => physicalEnergy (v r)) volume s t := by
  have ht : 0 < t := hs.trans_le hst
  haveI : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) t)) :=
    ⟨by simp only [Measure.restrict_apply_univ, Real.volume_Ioc]; finiteness⟩
  have hL2 : MemLp (fun r => criticalL2Representative (v r)) 2
      (volume.restrict (Ioc (0 : ℝ) t)) :=
    (hv.velocity_energy_class t ht).mono_exponent (by simp)
  have hE : IntegrableOn (fun r => physicalEnergy (v r)) (Ioc (0 : ℝ) t) volume := by
    apply hL2.norm.integrable_sq.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact criticalL2Representative_norm_sq (v r) (hv.velocity_L2 r hr.1.le)
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hst).mpr
    (hE.mono_set (Ioc_subset_Ioc hs.le le_rfl))

/-- Integrated weak momentum gives continuity of pairing with the moving
smooth test, rather than requiring that cross-pairing as a new hypothesis. -/
theorem CriticalIntegratedWeakMomentum.smooth_cross_continuousOn
    {ν : ℝ} {v : Velocity} (hv : CriticalIntegratedWeakMomentum ν v)
    (u : Velocity) (hu : CriticalPositiveSolenoidalTest u)
    (s t : ℝ) (hs : 0 < s) (hst : s ≤ t) :
    ContinuousOn (fun r => physicalFieldInner (v r) (u r)) (Icc s t) := by
  obtain ⟨hTime, hLap, hTransport⟩ := hv.test_integrable u hu s t hs hst
  have hI : IntervalIntegrable (criticalWeakMomentumIntegrand ν v u) volume s t :=
    (hTime.add (hLap.const_mul ν)).add hTransport
  have hP : ContinuousOn
      (fun r => ∫ q in s..r, criticalWeakMomentumIntegrand ν v u q) (Icc s t) := by
    simpa only [uIcc_of_le hst] using
      (intervalIntegral.continuousOn_primitive_interval' hI
        (left_mem_uIcc : s ∈ uIcc s t))
  have hC : ContinuousOn
      (fun r => physicalFieldInner (v s) (u s) +
        ∫ q in s..r, criticalWeakMomentumIntegrand ν v u q) (Icc s t) :=
    continuousOn_const.add hP
  apply hC.congr
  intro r hr
  have hm := hv.momentum u hu s r hs hr.1
  linarith only [hm]

/-- Actual relative energy is interval integrable on every positive slab. -/
theorem CriticalLerayHopf.relativeEnergy_intervalIntegrable
    {ν : ℝ} {a₀ : CriticalPhysicalL2} {v : Velocity}
    {G : ℝ → Vec → (Vec →L[ℝ] Vec)} (hv : CriticalLerayHopf ν a₀ v G)
    {u : Velocity} (hu : CriticalPositiveSolenoidalTest u)
    (s t : ℝ) (hs : 0 < s) (hst : s ≤ t) :
    IntervalIntegrable (fun r => physicalEnergy (v r - u r)) volume s t := by
  have hEu : ContinuousOn (fun r => physicalEnergy (u r)) (Icc s t) := by
    intro r hr
    exact (hu.physicalEnergy_hasDerivAt r (hs.trans_le hr.1)).continuousAt.continuousWithinAt
  have hCross := hv.momentum.smooth_cross_continuousOn u hu s t hs hst
  have hI : IntervalIntegrable
      (fun r => physicalEnergy (v r) + physicalEnergy (u r) -
        2 * physicalFieldInner (v r) (u r)) volume s t :=
    ((hv.physicalEnergy_intervalIntegrable s t hs hst).add
      (hEu.intervalIntegrable_of_Icc hst)).sub
        ((hCross.intervalIntegrable_of_Icc hst).const_mul 2)
  apply hI.congr
  intro r hr
  have hr' : r ∈ Ioc s t := by simpa only [uIoc_of_le hst] using hr
  have hrpos : 0 < r := hs.trans hr'.1
  exact (critical_physicalEnergy_sub (v r) (u r) (hv.velocity_L2 r hrpos.le)
    (critical_continuous_memLp_cube (u r) (hu.spatial_smooth hrpos).continuous 2)).symm

/-- The scalar comparison product is derived from the physical energy class,
smoothness and a continuous coefficient; no product-integrability certificate
is required. -/
theorem CRITICAL_RELATIVE_ENERGY_PRODUCT_INTERVAL_INTEGRABLE
    {ν : ℝ} {a₀ : CriticalPhysicalL2} {v : Velocity}
    {G : ℝ → Vec → (Vec →L[ℝ] Vec)} (hv : CriticalLerayHopf ν a₀ v G)
    {u : Velocity} (hu : CriticalPositiveSolenoidalTest u)
    (a : ℝ → ℝ) (s t : ℝ) (hs : 0 < s) (hst : s ≤ t)
    (ha : ContinuousOn a (Icc s t)) :
    IntervalIntegrable (fun r => a r * physicalEnergy (v r - u r)) volume s t := by
  exact (hv.relativeEnergy_intervalIntegrable hu s t hs hst).continuousOn_mul
    (by simpa only [uIcc_of_le hst] using ha)

end

end SingularClosure
