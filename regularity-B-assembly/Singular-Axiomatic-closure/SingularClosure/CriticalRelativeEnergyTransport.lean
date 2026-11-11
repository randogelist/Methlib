import SingularClosure.CriticalRelativeEnergy
import SingularClosure.CriticalRelativeNonlinear

/-! The physical relative-energy inequality with the actual rough advective
pairing.  Both the nonlinear polarization and the rough integration by parts
are discharged before invoking any quantitative transport estimate. -/

set_option autoImplicit false
set_option Elab.async true

open Set Filter MeasureTheory
open scoped BigOperators ContDiff ENNReal Topology Interval

namespace SingularClosure

noncomputable section

theorem CRITICAL_LH_SMOOTH_RELATIVE_ENERGY_TRANSPORT
    (ν : ℝ) (hν : 0 < ν) (a₀ : CriticalPhysicalL2)
    (v u : Velocity) (G : ℝ → Vec → (Vec →L[ℝ] Vec)) (p : Pressure)
    (hv : CriticalLerayHopf ν a₀ v G)
    (hu : CriticalPositiveSolenoidalTest u)
    (hp : ∀ r : ℝ, 0 < r → ContDiff ℝ ∞ (p r))
    (hpp : ∀ r : ℝ, 0 < r → SpatialPeriodic (p r))
    (hNSE : ∀ r : ℝ, 0 < r → ∀ x : Vec,
      timeDerivative u r x + convection (u r) x + gradient (p r) x =
        ν • laplacian (u r) x)
    (s t : ℝ) (hs : 0 < s) (hst : s ≤ t)
    (henergy : physicalEnergy (v t) +
      2 * ν * (∫ r in s..t, criticalGradientEnergy (G r)) ≤ physicalEnergy (v s)) :
    IntervalIntegrable (fun r => criticalGradientEnergy (G r - fderiv ℝ (u r))) volume s t ∧
    IntervalIntegrable (fun r => criticalRoughTransport (v r - u r)
      (G r - fderiv ℝ (u r)) (u r)) volume s t ∧
    physicalEnergy (v t - u t) +
      2 * ν * (∫ r in s..t, criticalGradientEnergy (G r - fderiv ℝ (u r))) ≤
      physicalEnergy (v s - u s) + 2 * (∫ r in s..t,
        criticalRoughTransport (v r - u r) (G r - fderiv ℝ (u r)) (u r)) := by
  have ht : 0 < t := hs.trans_le hst
  obtain ⟨hDI, hNI, hrelative⟩ := CRITICAL_LH_SMOOTH_RELATIVE_ENERGY_RAW
    ν hν a₀ v u G p hv hu hp hpp hNSE s t hs hst henergy
  have hH1 : ∀ᵐ r ∂volume.restrict (Ioc s t), CriticalPhysicalH1 (v r) (G r) :=
    ae_restrict_of_ae_restrict_of_subset
      (Ioc_subset_Ioc hs.le le_rfl) (hv.spatial_H1 t ht)
  have hnonlinear :
      (fun r => criticalWeakTransport (v r) (u r) -
        physicalFieldInner (v r) (convection (u r))) =ᵐ[volume.restrict (uIoc s t)]
      (fun r => -criticalRoughTransport (v r - u r)
        (G r - fderiv ℝ (u r)) (u r)) := by
    rw [uIoc_of_le hst]
    filter_upwards [hH1, ae_restrict_mem measurableSet_Ioc] with r hHr hr
    have hrpos : 0 < r := hs.trans hr.1
    have hus := hu.spatial_smooth hrpos
    have hvL2 := hv.velocity_L2 r hrpos.le
    have hdiv := hv.momentum.gradient_annihilation r hrpos
    rw [CRITICAL_RELATIVE_NONLINEAR_IDENTITY (v r) (u r) hvL2 hdiv
      hus (hu.periodic r hrpos) (hu.solenoidal r hrpos)]
    exact CRITICAL_ROUGH_TRANSPORT_SKEW (v r - u r) (G r - fderiv ℝ (u r)) (u r)
      (hHr.sub_smooth (u r) hus (hu.periodic r hrpos))
      (critical_gradient_annihilation_sub_smooth (v r) (u r) hvL2 hdiv
        hus (hu.periodic r hrpos) (hu.solenoidal r hrpos))
      hus (hu.periodic r hrpos)
  have hRI : IntervalIntegrable (fun r => criticalRoughTransport (v r - u r)
      (G r - fderiv ℝ (u r)) (u r)) volume s t := by
    apply hNI.neg.congr_ae
    filter_upwards [hnonlinear] with r hr
    exact neg_eq_iff_eq_neg.mpr hr
  have hNint : (∫ r in s..t, criticalWeakTransport (v r) (u r) -
      physicalFieldInner (v r) (convection (u r))) =
      -(∫ r in s..t, criticalRoughTransport (v r - u r)
        (G r - fderiv ℝ (u r)) (u r)) := by
    rw [intervalIntegral.integral_congr_ae hnonlinear, intervalIntegral.integral_neg]
  refine ⟨hDI, hRI, ?_⟩
  rw [hNint] at hrelative
  nlinarith only [hrelative]

end

end SingularClosure
