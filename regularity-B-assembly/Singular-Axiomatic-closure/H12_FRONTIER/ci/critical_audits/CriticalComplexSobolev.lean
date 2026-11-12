import SingularClosure.CriticalComplexSobolev

set_option autoImplicit false
set_option Elab.async false
open Set MeasureTheory Filter
open scoped BigOperators ContDiff Topology ENNReal Interval
namespace SingularClosure
noncomputable section

example (N : ℕ) (c : FourierCoeff) (j : Fin 3) :
    eLpNorm (complexFiniteSynthesis N c j) 2 (volume.restrict unitCube) ≤
      (ENNReal.ofReal (coefficientEnergy N c)) ^ (1 / 2 : ℝ) :=
  @SingularClosure.CRITICAL_COMPLEX_FINITE_L2 N c j

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.CRITICAL_COMPLEX_FINITE_L2"
#check @SingularClosure.CRITICAL_COMPLEX_FINITE_L2
#print axioms SingularClosure.CRITICAL_COMPLEX_FINITE_L2

example :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (N : ℕ) (c : FourierCoeff) (j : Fin 3),
      eLpNorm (complexFiniteSynthesis N c j) 6 (volume.restrict unitCube) ≤
        C * (ENNReal.ofReal (coefficientDissipation N c)) ^ (1 / 2 : ℝ) :=
  @SingularClosure.CRITICAL_COMPLEX_FINITE_L6

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.CRITICAL_COMPLEX_FINITE_L6"
#check @SingularClosure.CRITICAL_COMPLEX_FINITE_L6
#print axioms SingularClosure.CRITICAL_COMPLEX_FINITE_L6

end
end SingularClosure
