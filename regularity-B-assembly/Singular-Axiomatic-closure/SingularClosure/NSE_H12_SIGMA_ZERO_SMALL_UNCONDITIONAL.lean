import SingularClosure.SmallDataUniqueness
import SingularClosure.CriticalStrongLerayHopf
import SingularClosure.CriticalGlobalEnergyClass
import SingularClosure.CriticalGlobalSerrin
import SingularClosure.CriticalInitialPhysicalFourier

/-! Exact small-data closure for the actual periodic H1/2 space.
The same constructed solution supplies every conclusion. All auxiliary
analytic inputs are discharged by the imported proof spine. -/

set_option autoImplicit false
set_option Elab.async true
open Set MeasureTheory
open scoped Interval
namespace SingularClosure
noncomputable section

theorem NSE_H12_SIGMA_ZERO_SMALL_UNCONDITIONAL
    (ν : ℝ) (hν : 0 < ν) (a : CriticalSobolev 1) (ha : CriticalSigmaZero a)
    (hsmall : criticalNonlinearConstant * ‖a‖ < ν) :
    CriticalDatumAX6 ν a ∧ ∃ U : CriticalRegularSolution ν a,
      CriticalLerayHopf ν (criticalInitialPhysicalL2 a) U.lerayVelocity U.lerayGradient ∧
      U.lerayHopfUnique ∧
      PositiveSmoothNSE ν U.flow.velocity U.flow.pressure ∧
      (MemLp U.flow.threeHalfState 2 (volume.restrict (Ioi (0 : ℝ))) ∧
        (∫ t in Ioi (0 : ℝ), ‖U.flow.threeHalfState t‖ ^ 2) ≤ criticalDissipationBudget ν a) ∧
      (MemLp U.flow.negativeHalfDerivative 2 (volume.restrict (Ioi (0 : ℝ))) ∧
        (∫ t in Ioi (0 : ℝ), ‖U.flow.negativeHalfDerivative t‖ ^ 2) ≤
          criticalTimeDerivativeBudget ν a) ∧
      MemLp (fun t => criticalSpatialNorm 6 (U.flow.velocity t)) 4
        (volume.restrict (Ioi (0 : ℝ))) ∧
      (∀ T : ℝ, 0 < T →
        IntegrableOn (fun t => physicalDissipation (U.flow.velocity t) ^ 2)
          (Icc (0 : ℝ) T) volume ∧
        (∫ t in (0 : ℝ)..T, physicalDissipation (U.flow.velocity t) ^ 2) ≤
          (‖a‖ ^ 4 - ‖U.critical T‖ ^ 4) /
            (4 * (ν - criticalNonlinearConstant * ‖a‖))) := by
  obtain ⟨U, hW, hV, hQ⟩ :=
    SMALL_DATA_CRITICAL_GLOBAL_ENERGY_CLASS ν hν a ha hsmall
  have hδ : 0 < ν - criticalNonlinearConstant * ‖a‖ := sub_pos.mpr hsmall
  have hM : 0 ≤ ‖a‖ ^ 4 / (4 * (ν - criticalNonlinearConstant * ‖a‖)) :=
    div_nonneg (by positivity) (by positivity)
  have hS := U.serrin_global_memLp_of_quartic_budget
    (‖a‖ ^ 4 / (4 * (ν - criticalNonlinearConstant * ‖a‖))) hM
    (fun T hT => ⟨(hQ T hT).1, (hQ T hT).2.trans
      (div_le_div_of_nonneg_right (sub_le_self _ (by positivity)) (by positivity))⟩)
  have hSloc (T : ℝ) (hT : 0 < T) :
      MemLp (fun t => criticalSpatialNorm 6 (U.flow.velocity t)) 4
        (volume.restrict (Ioc (0 : ℝ) T)) :=
    U.serrin_time_memLp T (hQ T hT).1
  exact ⟨SMALL_DATA_AX6 ν hν a ha.reality ha.solenoidal ha.mean_zero hsmall,
    U, U.lerayHopf_of_quartic (fun T hT => (hQ T hT).1),
    U.lerayHopfUnique_of_serrin hν hSloc, U.physicalNSE, hW, hV, hS.1, hQ⟩

end
end SingularClosure
