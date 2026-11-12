import SingularClosure.CriticalStrongLerayHopf

set_option autoImplicit false
set_option Elab.async false
open Set MeasureTheory Filter
open scoped BigOperators ContDiff Topology ENNReal Interval
namespace SingularClosure
noncomputable section

example {ν : ℝ} {a : CriticalSobolev 1} (U : CriticalRegularSolution ν a)
    (hQ : ∀ T : ℝ, 0 < T →
      IntegrableOn (fun t => physicalDissipation (U.flow.velocity t) ^ 2)
        (Icc (0 : ℝ) T) volume) :
    CriticalLerayHopf ν (criticalInitialPhysicalL2 a)
      U.lerayVelocity U.lerayGradient :=
  @SingularClosure.CriticalRegularSolution.lerayHopf_of_quartic ν a U hQ

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.CriticalRegularSolution.lerayHopf_of_quartic"
#check @SingularClosure.CriticalRegularSolution.lerayHopf_of_quartic
#print axioms SingularClosure.CriticalRegularSolution.lerayHopf_of_quartic

end
end SingularClosure
