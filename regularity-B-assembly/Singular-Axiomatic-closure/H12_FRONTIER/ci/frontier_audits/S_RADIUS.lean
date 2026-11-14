import SingularClosure.H12Frontier.ConstantNormalization

/-! Concrete specialization; every nonlinear certificate is constructed from
proved physical inequalities. All registered datum hypotheses are retained. -/
set_option autoImplicit false
set_option Elab.async false
open Set MeasureTheory Filter
open scoped BigOperators Topology Interval NNReal ENNReal
namespace SingularClosure.H12Frontier
noncomputable section

example :
    ∀ (ν : ℝ) (hν : 0 < ν),
    ν / literatureK2 < (Real.sqrt 2 / literatureK2) * ν :=
  @SingularClosure.H12Frontier.literal_radius_strictly_enlarged

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.H12Frontier.literal_radius_strictly_enlarged"
#print axioms SingularClosure.H12Frontier.literal_radius_strictly_enlarged

end
end SingularClosure.H12Frontier
