import SingularClosure.CriticalPositiveFlow

set_option autoImplicit false
set_option Elab.async false
open Set MeasureTheory Filter
open scoped BigOperators ContDiff Topology ENNReal Interval
namespace SingularClosure
noncomputable section

example {ν : ℝ} (L : CriticalPositiveSobolevFlow ν) :
    PositiveSmoothNSE ν L.velocity L.pressure :=
  @SingularClosure.CRITICAL_POSITIVE_PHYSICAL_NSE ν L

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.CRITICAL_POSITIVE_PHYSICAL_NSE"
#check @SingularClosure.CRITICAL_POSITIVE_PHYSICAL_NSE
#print axioms SingularClosure.CRITICAL_POSITIVE_PHYSICAL_NSE

end
end SingularClosure
