import SingularClosure.H12Frontier.ProductMilestones

set_option autoImplicit false
set_option Elab.async false
open Set MeasureTheory Filter
open scoped BigOperators Topology Interval NNReal ENNReal
namespace SingularClosure.H12Frontier
noncomputable section

example :
    ∀ {ν T : ℝ} {N : ℕ} (hν : 0 ≤ ν) (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hsmall : nativeProduct * ‖a‖ < ν) (hT : 0 ≤ T)
    (g : GalerkinSolution ν (finiteSynthesis N (criticalCoeff 1 a)) N)
    {t : ℝ} (ht : t ∈ Icc 0 T),
    ‖g.criticalRhs (-1) t‖ ≤
      (ν + criticalTransportConstant * ‖a‖) * Real.sqrt (criticalEnergy 3 N (g.coeff t)) :=
  @SingularClosure.H12Frontier.PRODUCT_TIME_DERIVATIVE_POINTWISE

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.H12Frontier.PRODUCT_TIME_DERIVATIVE_POINTWISE"
#print axioms SingularClosure.H12Frontier.PRODUCT_TIME_DERIVATIVE_POINTWISE

example :
    ∀ {ν T : ℝ} {N : ℕ} (hν : 0 ≤ ν) (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hsmall : nativeProduct * ‖a‖ < ν) (hT : 0 ≤ T)
    (g : GalerkinSolution ν (finiteSynthesis N (criticalCoeff 1 a)) N)
    {t : ℝ} (ht : t ∈ Icc 0 T),
    ‖g.criticalRhs (-1) t‖ ^ 2 ≤
      (ν + criticalTransportConstant * ‖a‖) ^ 2 * criticalEnergy 3 N (g.coeff t) :=
  @SingularClosure.H12Frontier.PRODUCT_TIME_DERIVATIVE_SQUARE

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.H12Frontier.PRODUCT_TIME_DERIVATIVE_SQUARE"
#print axioms SingularClosure.H12Frontier.PRODUCT_TIME_DERIVATIVE_SQUARE

example :
    ∀ {ν T : ℝ} {N : ℕ} (hν : 0 ≤ ν) (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hsmall : nativeProduct * ‖a‖ < ν) (hT : 0 ≤ T)
    (g : GalerkinSolution ν (finiteSynthesis N (criticalCoeff 1 a)) N),
    (∫ t in (0 : ℝ)..T, ‖g.criticalRhs (-1) t‖ ^ 2) ≤
      (ν + criticalTransportConstant * ‖a‖) ^ 2 * ‖a‖ ^ 2 /
        (2 * (ν - nativeProduct * ‖a‖)) :=
  @SingularClosure.H12Frontier.PRODUCT_TIME_DERIVATIVE_BUDGET

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.H12Frontier.PRODUCT_TIME_DERIVATIVE_BUDGET"
#print axioms SingularClosure.H12Frontier.PRODUCT_TIME_DERIVATIVE_BUDGET

end
end SingularClosure.H12Frontier
