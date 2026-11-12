import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic
import QuasiFeffermanB.FourierEnergy
import QuasiFeffermanB.LHEnergy

/-!
The critical readout is the SQUARED homogeneous H^(1/2) norm.
Consequently its square is the fourth power of that norm.
All time integrals below are actual Bochner integrals.
-/

noncomputable section

open MeasureTheory Set

namespace QuasiFeffermanB

/-- Lebesgue measure on the strictly positive time interval before T. -/
def criticalTimeMeasure (T : ℝ) : Measure ℝ :=
  volume.restrict (Ioo 0 T)

/-- The pointwise interpolation inequality and kinetic bound give a
measurable integrable majorant for the critical fourth power. -/
theorem criticalFourthPower_integrable
    {α : Type*} [MeasurableSpace α] {m : Measure α}
    {kinetic gradient critical : α → ℝ} {M : ℝ}
    (hgradient : Integrable gradient m)
    (hcritical : AEStronglyMeasurable (fun t => critical t ^ 2) m)
    (hpoint : ∀ᵐ t ∂m,
      0 ≤ gradient t ∧ kinetic t ≤ M ∧
      critical t ^ 2 ≤ kinetic t * gradient t) :
    Integrable (fun t => critical t ^ 2) m := by
  apply (hgradient.const_mul M).mono' hcritical
  filter_upwards [hpoint] with t ht
  have hbound : critical t ^ 2 ≤ M * gradient t :=
    ht.2.2.trans (mul_le_mul_of_nonneg_right ht.2.1 ht.1)
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (critical t))] using hbound

/-- Actual time-integral fourth-power estimate. M is the squared L² norm
of the initial datum; the dissipation bound is the Leray--Hopf bound. -/
theorem criticalFourthPower_budget
    {α : Type*} [MeasurableSpace α] {m : Measure α}
    {kinetic gradient critical : α → ℝ} {M μ : ℝ}
    (hM : 0 ≤ M)
    (hgradient : Integrable gradient m)
    (hcritical : AEStronglyMeasurable (fun t => critical t ^ 2) m)
    (hpoint : ∀ᵐ t ∂m,
      0 ≤ gradient t ∧ kinetic t ≤ M ∧
      critical t ^ 2 ≤ kinetic t * gradient t)
    (hdissipation : (∫ t, gradient t ∂m) ≤ M / (2 * μ)) :
    (∫ t, critical t ^ 2 ∂m) ≤ M ^ 2 / (2 * μ) := by
  have hc := criticalFourthPower_integrable hgradient hcritical hpoint
  have hdom : ∀ᵐ t ∂m, critical t ^ 2 ≤ M * gradient t := by
    filter_upwards [hpoint] with t ht
    exact ht.2.2.trans (mul_le_mul_of_nonneg_right ht.2.1 ht.1)
  calc
    (∫ t, critical t ^ 2 ∂m) ≤ ∫ t, M * gradient t ∂m :=
      integral_mono_ae hc (hgradient.const_mul M) hdom
    _ = M * (∫ t, gradient t ∂m) := integral_const_mul _ _
    _ ≤ M * (M / (2 * μ)) := mul_le_mul_of_nonneg_left hdissipation hM
    _ = M ^ 2 / (2 * μ) := by ring

/-- The exact eventual-regularity cutoff in squared-energy coordinates. -/
def energyCutoff (M μ : ℝ) : ℝ :=
  M ^ 2 / (8 * Real.pi ^ 2 * μ ^ 5)

theorem energyCutoff_nonneg {M μ : ℝ} (hμ : 0 < μ) :
    0 ≤ energyCutoff M μ := by
  unfold energyCutoff
  positivity

/-- The authoritative extended Fourier profile is finite almost everywhere;
the real integral below therefore does not discard an infinite-energy set. -/
theorem LH_HALF_ENERGY_AE_FINITE
    {ν : ℝ} {a : SingularClosure.CriticalPhysicalL2}
    {u : SingularClosure.Velocity} {G : WeakGradientTrajectory}
    (hu : SingularClosure.CriticalLerayHopf ν a u G) {T : ℝ} (hT : 0 < T) :
    ∀ᵐ t ∂criticalTimeMeasure T, physicalHalfEnergy (u t) ≠ ⊤ := by
  have hH1 := ae_restrict_of_ae_restrict_of_subset Ioo_subset_Ioc_self (hu.spatial_H1 T hT)
  filter_upwards [hH1] with t ht
  exact physicalH1_halfEnergy_ne_top ht

theorem LH_HALF_ENERGY_AEMEASURABLE
    {ν : ℝ} {a : SingularClosure.CriticalPhysicalL2}
    {u : SingularClosure.Velocity} {G : WeakGradientTrajectory}
    (hu : SingularClosure.CriticalLerayHopf ν a u G) {T : ℝ} (hT : 0 < T) :
    AEMeasurable (fun t => physicalHalfEnergy (u t)) (criticalTimeMeasure T) := by
  apply physicalHalfEnergy_aemeasurable
  · have ht : ∀ᵐ t ∂criticalTimeMeasure T, t ∈ Ioo 0 T :=
      ae_restrict_mem measurableSet_Ioo
    filter_upwards [ht] with t ht
    exact hu.velocity_L2 t ht.1.le
  · exact (hu.velocity_energy_class T hT).aestronglyMeasurable.mono_measure
      (Measure.restrict_mono_set volume Ioo_subset_Ioc_self)

/-- Exact Q04 on the physical LH trajectory. Here the squared readout is
the fourth power of the homogeneous H(1/2) seminorm. -/
theorem LH_FOURTH_POWER_BUDGET
    {ν : ℝ} {a : SingularClosure.CriticalPhysicalL2}
    {u : SingularClosure.Velocity} {G : WeakGradientTrajectory}
    (hν : 0 < ν) (hu : SingularClosure.CriticalLerayHopf ν a u G)
    {T : ℝ} (hT : 0 < T) :
    Integrable (fun t => (physicalHalfEnergy (u t)).toReal ^ 2) (criticalTimeMeasure T) ∧
      (∫ t, (physicalHalfEnergy (u t)).toReal ^ 2 ∂criticalTimeMeasure T) ≤
        ‖a‖ ^ 4 / (2 * ν) := by
  obtain ⟨hkinetic, hdissipation⟩ := LH_ENERGY_BOUNDS hν hu
  obtain ⟨hDint, hDbound⟩ := hdissipation T hT
  have hD : Integrable (fun t => SingularClosure.criticalGradientEnergy (G t))
      (criticalTimeMeasure T) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hT.le).1 hDint
  have hcritical : AEStronglyMeasurable
      (fun t => (physicalHalfEnergy (u t)).toReal ^ 2) (criticalTimeMeasure T) :=
    ((LH_HALF_ENERGY_AEMEASURABLE hu hT).ennreal_toReal.pow_const 2).aestronglyMeasurable
  have hpoint : ∀ᵐ t ∂criticalTimeMeasure T,
      0 ≤ SingularClosure.criticalGradientEnergy (G t) ∧
      SingularClosure.physicalEnergy (u t) ≤ ‖a‖ ^ 2 ∧
      (physicalHalfEnergy (u t)).toReal ^ 2 ≤
        SingularClosure.physicalEnergy (u t) * SingularClosure.criticalGradientEnergy (G t) := by
    have hH1 := ae_restrict_of_ae_restrict_of_subset Ioo_subset_Ioc_self (hu.spatial_H1 T hT)
    have ht : ∀ᵐ t ∂criticalTimeMeasure T, t ∈ Ioo 0 T :=
      ae_restrict_mem measurableSet_Ioo
    filter_upwards [hH1, ht] with t hH1 ht
    exact ⟨SingularClosure.criticalGradientEnergy_nonneg _, hkinetic t ht.1.le,
      physicalH1_halfEnergy_midpoint hH1⟩
  refine ⟨criticalFourthPower_integrable hD hcritical hpoint, ?_⟩
  have hDbound' : (∫ t, SingularClosure.criticalGradientEnergy (G t)
      ∂criticalTimeMeasure T) ≤ ‖a‖ ^ 2 / (2 * ν) := by
    simpa only [criticalTimeMeasure, intervalIntegral.integral_of_le hT.le,
      integral_Ioc_eq_integral_Ioo] using hDbound
  have hb := criticalFourthPower_budget (sq_nonneg ‖a‖) hD hcritical hpoint hDbound'
  convert hb using 1 <;> ring

end QuasiFeffermanB

