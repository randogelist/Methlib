import SingularClosure.SmoothSixEnstrophy

set_option autoImplicit false
set_option Elab.async false
open Set MeasureTheory SingularClosure
open scoped BigOperators ContDiff ENNReal

noncomputable section

example : ∀ (a : Field)
    (ha : ContDiff ℝ ∞ a) (hp : SpatialPeriodic a),
    (∑ A : Fin 6, physicalEnstrophy (smoothSixChannel A a)) = physicalEnstrophy a :=
  @SingularClosure.SIX_CHANNEL_ENSTROPHY_EQ

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.SIX_CHANNEL_ENSTROPHY_EQ"
#check @SingularClosure.SIX_CHANNEL_ENSTROPHY_EQ
#print axioms SingularClosure.SIX_CHANNEL_ENSTROPHY_EQ

end
