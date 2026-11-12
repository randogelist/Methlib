import SingularClosure.Root
set_option autoImplicit false
set_option Elab.async false
open SingularClosure Set MeasureTheory Filter Metric
open scoped BigOperators Interval ContDiff ENNReal Topology
noncomputable section
example : AX6Statement → Fefferman_B_0_adjust :=
  @SingularClosure.ax6_implies_fefferman_B_0_adjust

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.ax6_implies_fefferman_B_0_adjust"
#check @SingularClosure.ax6_implies_fefferman_B_0_adjust
#print axioms SingularClosure.ax6_implies_fefferman_B_0_adjust
end
