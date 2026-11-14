import SingularClosure.GlobalStrongLimit
set_option autoImplicit false
set_option Elab.async false
open SingularClosure Set MeasureTheory Filter Metric
open scoped BigOperators Interval ContDiff ENNReal Topology
noncomputable section
example : ∀ (hAX6 : AX6Statement)
    (ν : ℝ) (hν : 0 < ν) (a : Field) (ha : SmoothSigmaZero a),
    Nonempty (GlobalGalerkinStrongLimit ν a ha) :=
  @SingularClosure.GALERKIN_GLOBAL_STRONG_LIMIT

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.GALERKIN_GLOBAL_STRONG_LIMIT"
#check @SingularClosure.GALERKIN_GLOBAL_STRONG_LIMIT
#print axioms SingularClosure.GALERKIN_GLOBAL_STRONG_LIMIT
end
