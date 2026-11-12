import SingularClosure.SmallDataAX6Closure

set_option autoImplicit false
set_option Elab.async false
open Set MeasureTheory Filter
open scoped BigOperators ContDiff Topology ENNReal Interval
namespace SingularClosure
noncomputable section

example {ν T : ℝ} {N : ℕ} (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hsmall : criticalNonlinearConstant * ‖a‖ < ν) (hT : 0 ≤ T)
    (g : GalerkinSolution ν (finiteSynthesis N (criticalCoeff 1 a)) N) :
    budget6 N g.coeff T ≤
      ENNReal.ofReal (‖a‖ ^ 4 / (4 * (ν - criticalNonlinearConstant * ‖a‖))) :=
  @SingularClosure.SMALL_DATA_SIX_CHANNEL_BUDGET ν T N a hreal hsmall hT g

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.SMALL_DATA_SIX_CHANNEL_BUDGET"
#check @SingularClosure.SMALL_DATA_SIX_CHANNEL_BUDGET
#print axioms SingularClosure.SMALL_DATA_SIX_CHANNEL_BUDGET

example (ν : ℝ) (_hν : 0 < ν) (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (_hsol : SpectralSolenoidal (criticalCoeff 1 a))
    (_hzero : SpectralMeanZero (criticalCoeff 1 a))
    (hsmall : criticalNonlinearConstant * ‖a‖ < ν) :
    CriticalDatumAX6 ν a :=
  @SingularClosure.SMALL_DATA_AX6 ν _hν a hreal _hsol _hzero hsmall

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.SMALL_DATA_AX6"
#check @SingularClosure.SMALL_DATA_AX6
#print axioms SingularClosure.SMALL_DATA_AX6

end
end SingularClosure
