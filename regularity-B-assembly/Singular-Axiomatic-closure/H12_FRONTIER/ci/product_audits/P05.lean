import SingularClosure.H12Frontier.ProductConstants

set_option autoImplicit false
set_option Elab.async false
open Set MeasureTheory Filter
open scoped BigOperators Topology Interval NNReal ENNReal
namespace SingularClosure.H12Frontier
noncomputable section

example :
    ∀ (ν : ℝ) (a : CriticalSobolev 1),
    productDissipationConstant ν a = ‖a‖ ^ 2 / (2 * (ν - nativeProduct * ‖a‖)) :=
  @SingularClosure.H12Frontier.productDissipationConstant_eq

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.H12Frontier.productDissipationConstant_eq"
#print axioms SingularClosure.H12Frontier.productDissipationConstant_eq

example :
    ∀ (ν : ℝ) (a : CriticalSobolev 1),
    productDerivativeConstant ν a =
      (ν + criticalTransportConstant * ‖a‖) ^ 2 * ‖a‖ ^ 2 /
        (2 * (ν - nativeProduct * ‖a‖)) :=
  @SingularClosure.H12Frontier.productDerivativeConstant_eq

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.H12Frontier.productDerivativeConstant_eq"
#print axioms SingularClosure.H12Frontier.productDerivativeConstant_eq

example :
    ∀ (ν : ℝ) (a : CriticalSobolev 1)
    (hsmall : nativeProduct * ‖a‖ < ν),
    0 < ν - nativeProduct * ‖a‖ ∧
    0 ≤ productDissipationConstant ν a ∧
    0 ≤ productDerivativeConstant ν a ∧
    productDissipationConstant ν a = ‖a‖ ^ 2 / (2 * (ν - nativeProduct * ‖a‖)) ∧
    productDerivativeConstant ν a =
      (ν + criticalTransportConstant * ‖a‖) ^ 2 * ‖a‖ ^ 2 /
        (2 * (ν - nativeProduct * ‖a‖)) :=
  @SingularClosure.H12Frontier.PRODUCT_MARGIN_AND_BUDGETS

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.H12Frontier.PRODUCT_MARGIN_AND_BUDGETS"
#print axioms SingularClosure.H12Frontier.PRODUCT_MARGIN_AND_BUDGETS

end
end SingularClosure.H12Frontier
