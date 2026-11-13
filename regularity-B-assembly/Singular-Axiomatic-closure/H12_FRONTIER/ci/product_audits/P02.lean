import SingularClosure.H12Frontier.ProductConstants

set_option autoImplicit false
set_option Elab.async false
open Set MeasureTheory Filter
open scoped BigOperators Topology Interval NNReal ENNReal
namespace SingularClosure.H12Frontier
noncomputable section

example :
    literatureK2 = 2 * Real.sqrt Real.pi * paperScale ^ 3 * nativeProduct :=
  @SingularClosure.H12Frontier.product_literatureK2_eq

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.H12Frontier.product_literatureK2_eq"
#print axioms SingularClosure.H12Frontier.product_literatureK2_eq

example :
    0 < nativeProduct ∧ 0 < literatureK2 ∧
    frontierConstant = paperScale ^ 3 * nativeProduct ∧
    literatureK2 = 2 * Real.sqrt Real.pi * paperScale ^ 3 * nativeProduct :=
  @SingularClosure.H12Frontier.PRODUCT_CONSTANT_IDENTITY

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.H12Frontier.PRODUCT_CONSTANT_IDENTITY"
#print axioms SingularClosure.H12Frontier.PRODUCT_CONSTANT_IDENTITY

end
end SingularClosure.H12Frontier
