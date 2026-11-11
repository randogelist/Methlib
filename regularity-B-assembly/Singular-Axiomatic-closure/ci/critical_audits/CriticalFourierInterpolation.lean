import SingularClosure.CriticalFourierInterpolation

set_option autoImplicit false
set_option Elab.async false
open Set MeasureTheory Filter
open scoped BigOperators ContDiff Topology ENNReal Interval
namespace SingularClosure
noncomputable section

example (N : ℕ) (c : FourierCoeff) :
    criticalEnergy 2 N c ^ 2 ≤ criticalEnergy 1 N c * criticalEnergy 3 N c :=
  @SingularClosure.criticalEnergy_interpolation N c

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.criticalEnergy_interpolation"
#check @SingularClosure.criticalEnergy_interpolation
#print axioms SingularClosure.criticalEnergy_interpolation

end
end SingularClosure
