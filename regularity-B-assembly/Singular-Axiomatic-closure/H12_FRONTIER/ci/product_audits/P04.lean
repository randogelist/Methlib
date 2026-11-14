import SingularClosure.H12Frontier.ProductNormalization

set_option autoImplicit false
set_option Elab.async false
open Set MeasureTheory Filter
open scoped BigOperators Topology Interval NNReal ENNReal
namespace SingularClosure.H12Frontier
noncomputable section

example :
    ∀ (ν : ℝ) (a : CriticalSobolev 1)
    (hz : SpectralMeanZero (criticalCoeff 1 a)),
    paperNorm 1 a < (Real.sqrt 2 * paperScale ^ 3 / literatureK2) * ν ↔
      nativeProduct * ‖a‖ < ν :=
  @SingularClosure.H12Frontier.PRODUCT_SMALLNESS_IFF

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.H12Frontier.PRODUCT_SMALLNESS_IFF"
#print axioms SingularClosure.H12Frontier.PRODUCT_SMALLNESS_IFF

example :
    1 < paperScale ^ 3 :=
  @SingularClosure.H12Frontier.product_scale_cube_gt_one

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.H12Frontier.product_scale_cube_gt_one"
#print axioms SingularClosure.H12Frontier.product_scale_cube_gt_one

example :
    ∀ (ν : ℝ) (hν : 0 < ν),
    ν / nativeProduct = paperScale ^ 3 * (ν / frontierConstant) ∧
    ν / frontierConstant < ν / nativeProduct :=
  @SingularClosure.H12Frontier.PRODUCT_RADIUS_RATIO

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.H12Frontier.PRODUCT_RADIUS_RATIO"
#print axioms SingularClosure.H12Frontier.PRODUCT_RADIUS_RATIO

end
end SingularClosure.H12Frontier
