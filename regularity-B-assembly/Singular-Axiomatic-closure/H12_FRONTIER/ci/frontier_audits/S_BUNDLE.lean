import SingularClosure.H12Frontier.LiteratureConstants

/-! Concrete specialization; every nonlinear certificate is constructed from
proved physical inequalities. All registered datum hypotheses are retained. -/
set_option autoImplicit false
set_option Elab.async false
open Set MeasureTheory Filter
open scoped BigOperators Topology Interval NNReal ENNReal
namespace SingularClosure.H12Frontier
noncomputable section

example :
    0 < CSZero ∧ 0 < CSHalf ∧ 0 < CSOne ∧
    (∀ N c, eLpNorm (dilatedField paperScale (finiteSynthesis N c)) 3
      (volume.restrict (dilatedCube paperScale)) ≤
        ENNReal.ofReal CSHalf * ENNReal.ofReal (paperFiniteNorm 1 N c)) ∧
    (∀ N c, SpectralReality c →
      eLpNorm (dilatedField paperScale (finiteSynthesis N c)) 6
        (volume.restrict (dilatedCube paperScale)) ≤
          ENNReal.ofReal CSOne * ENNReal.ofReal (paperFiniteNorm 2 N c)) ∧
    (∀ N c, SpectralReality c →
      eLpNorm (dilatedField paperScale (finiteSynthesis N c)) 2
        (volume.restrict (dilatedCube paperScale)) =
          ENNReal.ofReal CSZero * ENNReal.ofReal (paperFiniteNorm 0 N c)) :=
  @SingularClosure.H12Frontier.CONCRETE_LITERATURE_SOBOLEV_BUNDLE

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.H12Frontier.CONCRETE_LITERATURE_SOBOLEV_BUNDLE"
#print axioms SingularClosure.H12Frontier.CONCRETE_LITERATURE_SOBOLEV_BUNDLE

end
end SingularClosure.H12Frontier
