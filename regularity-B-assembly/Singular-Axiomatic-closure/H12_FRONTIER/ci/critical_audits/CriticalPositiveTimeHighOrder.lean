import SingularClosure.CriticalPositiveTimeHighOrder

set_option autoImplicit false
set_option Elab.async false
open Set MeasureTheory Filter
open scoped BigOperators ContDiff Topology ENNReal Interval
namespace SingularClosure
noncomputable section

example (ν : ℝ) (hν : 0 < ν) (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hsmall : criticalNonlinearConstant * ‖a‖ < ν)
    (m : ℕ) (τ T : ℝ) (hτ : 0 < τ) (hτT : τ < T) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ,
      ∀ g : GalerkinSolution ν (finiteSynthesis N (criticalCoeff 1 a)) N,
      ∀ t ∈ Icc τ T, highOrderEnergy m N (g.coeff t) +
        ν * (∫ s in τ..t, highOrderEnergy (m + 1) N (g.coeff s)) ≤ B :=
  @SingularClosure.SMALL_DATA_POSITIVE_TIME_ALL_ORDERS ν hν a hreal hsmall m τ T hτ hτT

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.SMALL_DATA_POSITIVE_TIME_ALL_ORDERS"
#check @SingularClosure.SMALL_DATA_POSITIVE_TIME_ALL_ORDERS
#print axioms SingularClosure.SMALL_DATA_POSITIVE_TIME_ALL_ORDERS

end
end SingularClosure
