import SingularClosure.CriticalStrongLerayHopfGradient
import SingularClosure.CriticalClassicalWeakMomentum

/-! The constructed positive-time strong flow, with its actual rough L2 trace
at zero, belongs to the physical Leray--Hopf class. Every record field follows
from the established evolution, trace, energy and measurability theorems. -/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory Filter
open scoped ContDiff ENNReal Topology Interval

namespace SingularClosure

noncomputable section

/-- Membership retains the same constructed solution. The finite physical
quartic integral is discharged by the quantitative small-data construction. -/
theorem CriticalRegularSolution.lerayHopf_of_quartic
    {ν : ℝ} {a : CriticalSobolev 1} (U : CriticalRegularSolution ν a)
    (hQ : ∀ T : ℝ, 0 < T →
      IntegrableOn (fun t => physicalDissipation (U.flow.velocity t) ^ 2)
        (Icc (0 : ℝ) T) volume) :
    CriticalLerayHopf ν (criticalInitialPhysicalL2 a)
      U.lerayVelocity U.lerayGradient := by
  have hu : CriticalPositiveSolenoidalTest U.flow.velocity := {
    smooth := U.flow.velocity_spacetime_smooth
    periodic := fun t ht => (U.flow.velocity_smoothSigmaZero t ht).periodic
    solenoidal := fun t ht => (U.flow.velocity_smoothSigmaZero t ht).divergence_free
  }
  have hp (t : ℝ) (ht : 0 < t) : ContDiff ℝ ∞ (U.flow.pressure t) :=
    fullTransportPressure_contDiff (U.flow.state 0 t) (U.flow.state_all_mem t ht)
      (U.flow.reality t ht) (U.flow.solenoidal t ht)
  have hm : CriticalIntegratedWeakMomentum ν U.lerayVelocity :=
    (CRITICAL_CLASSICAL_NSE_INTEGRATED_WEAK_MOMENTUM ν U.flow.velocity U.flow.pressure
      hu hp (fun t _ => fullTransportPressure_periodic (U.flow.state 0 t))
      U.flow.physical_equation).congr_positive (fun t ht => U.lerayVelocity_of_pos ht)
  have hQnonneg (T : ℝ) (hT : 0 ≤ T) :
      IntegrableOn (fun t => physicalDissipation (U.flow.velocity t) ^ 2)
        (Icc (0 : ℝ) T) volume :=
    (hQ (T + 1) (by linarith)).mono_set (Icc_subset_Icc le_rfl (by linarith))
  refine {
    momentum := hm
    velocity_L2 := fun t _ => U.lerayVelocity_memLp t
    velocity_energy_class := fun T _ => U.leray_velocity_energy_class T
    gradient_energy_class := fun T hT => U.leray_gradient_energy_class T hT.le (hQ T hT)
    initial := Eventually.of_forall (fun x => congrFun U.lerayVelocity_zero x)
    weak_continuity := fun φ hφ => U.leray_weak_continuity φ hφ
    strong_trace := U.leray_strong_trace
    spatial_H1 := fun T _ => U.leray_spatial_H1 T
    dissipation_integrable := fun T hT => U.leray_dissipation_integrable T hT.le (hQ T hT)
    energy_initial := fun t ht => (U.leray_energy_initial_eq t ht (hQnonneg t ht)).le
    energy_intervals := ?_
  }
  intro T hT
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  intro t ht
  exact (U.leray_energy_interval_eq T hT.le (hQ T hT) s t hs.1.le ht.1 ht.2).le

end

end SingularClosure
