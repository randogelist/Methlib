import SingularClosure.H12Frontier.ProductMilestones

set_option autoImplicit false
set_option Elab.async false
open Set MeasureTheory Filter
open scoped BigOperators Topology Interval NNReal ENNReal
namespace SingularClosure.H12Frontier
noncomputable section

example :
    ∀ (ν : ℝ) (hν : 0 < ν) (a : CriticalSobolev 1) (ha : CriticalSigmaZero a)
    (hsmall : nativeProduct * ‖a‖ < ν),
    ∃ U : CriticalRegularSolution ν a,
      (MemLp U.flow.threeHalfState 2 (volume.restrict (Ioi (0 : ℝ))) ∧
        (∫ t in Ioi (0 : ℝ), ‖U.flow.threeHalfState t‖ ^ 2) ≤ (Replay.dissipationConstant nativeProductCertificate) ν a) ∧
      (MemLp U.flow.negativeHalfDerivative 2 (volume.restrict (Ioi (0 : ℝ))) ∧
        (∫ t in Ioi (0 : ℝ), ‖U.flow.negativeHalfDerivative t‖ ^ 2) ≤
          (Replay.derivativeConstant nativeProductCertificate) ν a) ∧
      (∀ T : ℝ, 0 < T →
        IntegrableOn (fun t => physicalDissipation (U.flow.velocity t) ^ 2)
          (Icc (0 : ℝ) T) volume ∧
        (∫ t in (0 : ℝ)..T, physicalDissipation (U.flow.velocity t) ^ 2) ≤
          (‖a‖ ^ 4 - ‖U.critical T‖ ^ 4) /
            (4 * (ν - nativeProduct * ‖a‖))) :=
  @SingularClosure.H12Frontier.PRODUCT_GLOBAL_ENERGY_CLASS

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.H12Frontier.PRODUCT_GLOBAL_ENERGY_CLASS"
#print axioms SingularClosure.H12Frontier.PRODUCT_GLOBAL_ENERGY_CLASS

end
end SingularClosure.H12Frontier
