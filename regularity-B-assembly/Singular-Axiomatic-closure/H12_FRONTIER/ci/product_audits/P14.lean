import SingularClosure.H12Frontier.ProductMilestones

set_option autoImplicit false
set_option Elab.async false
open Set MeasureTheory Filter
open scoped BigOperators Topology Interval NNReal ENNReal
namespace SingularClosure.H12Frontier
noncomputable section

example :
    ∀ (ν : ℝ) (hν : 0 < ν) (a : CriticalSobolev 1)
    (hsmall : nativeProduct * ‖a‖ < ν)
    (U : CriticalRegularSolution ν a)
    (hQ : ∀ T : ℝ, 0 < T →
      IntegrableOn (fun t => physicalDissipation (U.flow.velocity t) ^ 2)
        (Icc (0 : ℝ) T) volume ∧
      (∫ t in (0 : ℝ)..T, physicalDissipation (U.flow.velocity t) ^ 2) ≤
        (‖a‖ ^ 4 - ‖U.critical T‖ ^ 4) /
          (4 * (ν - nativeProduct * ‖a‖))),
    CriticalLerayHopf ν (criticalInitialPhysicalL2 a) U.lerayVelocity U.lerayGradient ∧
    U.lerayHopfUnique ∧
    PositiveSmoothNSE ν U.flow.velocity U.flow.pressure ∧
    MemLp (fun t => criticalSpatialNorm 6 (U.flow.velocity t)) 4
      (volume.restrict (Ioi (0 : ℝ))) :=
  @SingularClosure.H12Frontier.PRODUCT_SERRIN_LERAYHOPF

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.H12Frontier.PRODUCT_SERRIN_LERAYHOPF"
#print axioms SingularClosure.H12Frontier.PRODUCT_SERRIN_LERAYHOPF

end
end SingularClosure.H12Frontier
