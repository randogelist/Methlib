import SingularClosure.H12Frontier.NonlinearBound
import SingularClosure.H12Frontier.ReplayClosure
import SingularClosure.H12Frontier.LimitMilestones

/-! Concrete specialization; every nonlinear certificate is constructed from
proved physical inequalities. All registered datum hypotheses are retained. -/
set_option autoImplicit false
set_option Elab.async true
open Set MeasureTheory Filter
open scoped BigOperators Topology Interval NNReal ENNReal
namespace SingularClosure.H12Frontier
noncomputable section

theorem FRONTIER_H12_NATIVE :
    ∀ (ν : ℝ) (hν : 0 < ν) (a : CriticalSobolev 1) (ha : CriticalSigmaZero a)
    (hsmall : frontierConstant * ‖a‖ < ν),
    CriticalDatumAX6 ν a ∧ ∃ U : CriticalRegularSolution ν a,
      CriticalLerayHopf ν (criticalInitialPhysicalL2 a) U.lerayVelocity U.lerayGradient ∧
      U.lerayHopfUnique ∧
      PositiveSmoothNSE ν U.flow.velocity U.flow.pressure ∧
      (MemLp U.flow.threeHalfState 2 (volume.restrict (Ioi (0 : ℝ))) ∧
        (∫ t in Ioi (0 : ℝ), ‖U.flow.threeHalfState t‖ ^ 2) ≤ frontierDissipationConstant ν a) ∧
      (MemLp U.flow.negativeHalfDerivative 2 (volume.restrict (Ioi (0 : ℝ))) ∧
        (∫ t in Ioi (0 : ℝ), ‖U.flow.negativeHalfDerivative t‖ ^ 2) ≤
          frontierDerivativeConstant ν a) ∧
      MemLp (fun t => criticalSpatialNorm 6 (U.flow.velocity t)) 4
        (volume.restrict (Ioi (0 : ℝ))) ∧
      (∀ T : ℝ, 0 < T →
        IntegrableOn (fun t => physicalDissipation (U.flow.velocity t) ^ 2)
          (Icc (0 : ℝ) T) volume ∧
        (∫ t in (0 : ℝ)..T, physicalDissipation (U.flow.velocity t) ^ 2) ≤
          (‖a‖ ^ 4 - ‖U.critical T‖ ^ 4) /
            (4 * (ν - frontierConstant * ‖a‖))) :=
  @Replay.fullClosure frontierCertificate

theorem FRONTIER_H12 :
    ∀ (ν : ℝ) (hν : 0 < ν) (a : CriticalSobolev 1) (ha : CriticalSigmaZero a)
    (hsmall : paperNorm 1 a < (Real.sqrt 2 / literatureK2) * ν),
    CriticalDatumAX6 ν a ∧ ∃ U : CriticalRegularSolution ν a,
      CriticalLerayHopf ν (criticalInitialPhysicalL2 a) U.lerayVelocity U.lerayGradient ∧
      U.lerayHopfUnique ∧
      PositiveSmoothNSE ν U.flow.velocity U.flow.pressure ∧
      (MemLp U.flow.threeHalfState 2 (volume.restrict (Ioi (0 : ℝ))) ∧
        (∫ t in Ioi (0 : ℝ), ‖U.flow.threeHalfState t‖ ^ 2) ≤ frontierDissipationConstant ν a) ∧
      (MemLp U.flow.negativeHalfDerivative 2 (volume.restrict (Ioi (0 : ℝ))) ∧
        (∫ t in Ioi (0 : ℝ), ‖U.flow.negativeHalfDerivative t‖ ^ 2) ≤
          frontierDerivativeConstant ν a) ∧
      MemLp (fun t => criticalSpatialNorm 6 (U.flow.velocity t)) 4
        (volume.restrict (Ioi (0 : ℝ))) ∧
      (∀ T : ℝ, 0 < T →
        IntegrableOn (fun t => physicalDissipation (U.flow.velocity t) ^ 2)
          (Icc (0 : ℝ) T) volume ∧
        (∫ t in (0 : ℝ)..T, physicalDissipation (U.flow.velocity t) ^ 2) ≤
          (‖a‖ ^ 4 - ‖U.critical T‖ ^ 4) /
            (4 * (ν - frontierConstant * ‖a‖))) := by
  intro ν hν a ha hsmall
  exact FRONTIER_H12_NATIVE ν hν a ha
    ((FRONTIER_H12_SMALLNESS_IFF ν a ha.mean_zero).mp hsmall)

end
end SingularClosure.H12Frontier
