import SingularClosure.CriticalTimeDerivative

set_option autoImplicit false
set_option Elab.async false
open Set MeasureTheory Filter
open scoped BigOperators ContDiff Topology ENNReal Interval
namespace SingularClosure
noncomputable section

example {ν T : ℝ} {N : ℕ} (hν : 0 ≤ ν) (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hsmall : criticalNonlinearConstant * ‖a‖ < ν) (hT : 0 ≤ T)
    (g : GalerkinSolution ν (finiteSynthesis N (criticalCoeff 1 a)) N) :
    (∫ t in (0 : ℝ)..T, ‖g.criticalRhs (-1) t‖ ^ 2) ≤
      (ν + criticalTransportConstant * ‖a‖) ^ 2 * ‖a‖ ^ 2 /
        (2 * (ν - criticalNonlinearConstant * ‖a‖)) :=
  @SingularClosure.CRITICAL_GALERKIN_TIME_DERIVATIVE_BUDGET ν T N hν a hreal hsmall hT g

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.CRITICAL_GALERKIN_TIME_DERIVATIVE_BUDGET"
#check @SingularClosure.CRITICAL_GALERKIN_TIME_DERIVATIVE_BUDGET
#print axioms SingularClosure.CRITICAL_GALERKIN_TIME_DERIVATIVE_BUDGET

end
end SingularClosure
