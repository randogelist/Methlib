import SingularClosure.CriticalSobolev

set_option autoImplicit false
set_option Elab.async false
open Set MeasureTheory Filter
open scoped BigOperators ContDiff Topology ENNReal Interval
namespace SingularClosure
noncomputable section

example :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (N : ℕ) (c : FourierCoeff),
      eLpNorm (finiteSynthesis N c) 3 (volume.restrict unitCube) ≤
        C * (ENNReal.ofReal (criticalEnergy 1 N c)) ^ (1 / 2 : ℝ) :=
  @SingularClosure.FINITE_CRITICAL_HHALF_L3

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.FINITE_CRITICAL_HHALF_L3"
#check @SingularClosure.FINITE_CRITICAL_HHALF_L3
#print axioms SingularClosure.FINITE_CRITICAL_HHALF_L3

end
end SingularClosure
