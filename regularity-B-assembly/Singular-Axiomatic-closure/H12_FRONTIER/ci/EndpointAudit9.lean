import SingularClosure.GlobalSmoothBootstrap
set_option autoImplicit false
set_option Elab.async false
open SingularClosure Set MeasureTheory Filter Metric
open scoped BigOperators Interval ContDiff ENNReal Topology
noncomputable section
example : ∀ {ν : ℝ} {a : Field} {ha : SmoothSigmaZero a} (L : GlobalGalerkinStrongLimit ν a ha),
    ContDiffOn ℝ ∞ (fun z : ℝ × Vec => L.velocity z.1 z.2) forwardSpacetime :=
  @SingularClosure.GLOBAL_STRONG_SMOOTH_BOOTSTRAP

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.GLOBAL_STRONG_SMOOTH_BOOTSTRAP"
#check @SingularClosure.GLOBAL_STRONG_SMOOTH_BOOTSTRAP
#print axioms SingularClosure.GLOBAL_STRONG_SMOOTH_BOOTSTRAP
end
