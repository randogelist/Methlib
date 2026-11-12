import SingularClosure.H12Frontier.ReplayClosure
set_option autoImplicit false
set_option Elab.async false
open Set MeasureTheory Filter
open scoped BigOperators Topology Interval NNReal ENNReal
namespace SingularClosure.H12Frontier.Replay
noncomputable section

example : ∀ (cert : NonlinearCertificate)
    (ν : ℝ) (hν : 0 < ν) (a : CriticalSobolev 1) (ha : CriticalSigmaZero a)
    (hsmall : cert.constant * ‖a‖ < ν),
    ∃ U : CriticalRegularSolution ν a,
      (MemLp U.flow.threeHalfState 2 (volume.restrict (Ioi (0 : ℝ))) ∧
        (∫ t in Ioi (0 : ℝ), ‖U.flow.threeHalfState t‖ ^ 2) ≤ (dissipationConstant cert) ν a) ∧
      (MemLp U.flow.negativeHalfDerivative 2 (volume.restrict (Ioi (0 : ℝ))) ∧
        (∫ t in Ioi (0 : ℝ), ‖U.flow.negativeHalfDerivative t‖ ^ 2) ≤
          (derivativeConstant cert) ν a) ∧
      (∀ T : ℝ, 0 < T →
        IntegrableOn (fun t => physicalDissipation (U.flow.velocity t) ^ 2)
          (Icc (0 : ℝ) T) volume ∧
        (∫ t in (0 : ℝ)..T, physicalDissipation (U.flow.velocity t) ^ 2) ≤
          (‖a‖ ^ 4 - ‖U.critical T‖ ^ 4) /
            (4 * (ν - cert.constant * ‖a‖))) :=
  @SingularClosure.H12Frontier.Replay.globalEnergyClass

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.H12Frontier.Replay.globalEnergyClass"
#print axioms SingularClosure.H12Frontier.Replay.globalEnergyClass

example : ∀ (cert : NonlinearCertificate)
    (ν : ℝ) (hν : 0 < ν) (a : CriticalSobolev 1) (ha : CriticalSigmaZero a)
    (hsmall : cert.constant * ‖a‖ < ν),
    CriticalDatumAX6 ν a ∧ ∃ U : CriticalRegularSolution ν a,
      CriticalLerayHopf ν (criticalInitialPhysicalL2 a) U.lerayVelocity U.lerayGradient ∧
      U.lerayHopfUnique ∧
      PositiveSmoothNSE ν U.flow.velocity U.flow.pressure ∧
      (MemLp U.flow.threeHalfState 2 (volume.restrict (Ioi (0 : ℝ))) ∧
        (∫ t in Ioi (0 : ℝ), ‖U.flow.threeHalfState t‖ ^ 2) ≤ (dissipationConstant cert) ν a) ∧
      (MemLp U.flow.negativeHalfDerivative 2 (volume.restrict (Ioi (0 : ℝ))) ∧
        (∫ t in Ioi (0 : ℝ), ‖U.flow.negativeHalfDerivative t‖ ^ 2) ≤
          (derivativeConstant cert) ν a) ∧
      MemLp (fun t => criticalSpatialNorm 6 (U.flow.velocity t)) 4
        (volume.restrict (Ioi (0 : ℝ))) ∧
      (∀ T : ℝ, 0 < T →
        IntegrableOn (fun t => physicalDissipation (U.flow.velocity t) ^ 2)
          (Icc (0 : ℝ) T) volume ∧
        (∫ t in (0 : ℝ)..T, physicalDissipation (U.flow.velocity t) ^ 2) ≤
          (‖a‖ ^ 4 - ‖U.critical T‖ ^ 4) /
            (4 * (ν - cert.constant * ‖a‖))) :=
  @SingularClosure.H12Frontier.Replay.fullClosure

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.H12Frontier.Replay.fullClosure"
#print axioms SingularClosure.H12Frontier.Replay.fullClosure

end
end SingularClosure.H12Frontier.Replay
