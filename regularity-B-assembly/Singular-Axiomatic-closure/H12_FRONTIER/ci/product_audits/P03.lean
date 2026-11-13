import SingularClosure.H12Frontier.ProductNormalization

set_option autoImplicit false
set_option Elab.async false
open Set MeasureTheory Filter
open scoped BigOperators Topology Interval NNReal ENNReal
namespace SingularClosure.H12Frontier
noncomputable section

example :
    nativeProduct * Real.sqrt paperScale =
      literatureK2 / (Real.sqrt 2 * paperScale ^ 3) :=
  @SingularClosure.H12Frontier.product_coefficient_normalization

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.H12Frontier.product_coefficient_normalization"
#print axioms SingularClosure.H12Frontier.product_coefficient_normalization

example :
    ∀ (a : CriticalSobolev 1)
    (hz : SpectralMeanZero (criticalCoeff 1 a)),
    nativeProduct * ‖a‖ =
      (literatureK2 / (Real.sqrt 2 * paperScale ^ 3)) * paperNorm 1 a :=
  @SingularClosure.H12Frontier.PRODUCT_COEFFICIENT_NORM_IDENTITY

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.H12Frontier.PRODUCT_COEFFICIENT_NORM_IDENTITY"
#print axioms SingularClosure.H12Frontier.PRODUCT_COEFFICIENT_NORM_IDENTITY

end
end SingularClosure.H12Frontier
