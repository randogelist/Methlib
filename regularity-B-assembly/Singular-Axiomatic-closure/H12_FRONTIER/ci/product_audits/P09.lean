import SingularClosure.H12Frontier.ProductMilestones

set_option autoImplicit false
set_option Elab.async false
open Set MeasureTheory Filter
open scoped BigOperators Topology Interval NNReal ENNReal
namespace SingularClosure.H12Frontier
noncomputable section

example :
    ∀ {ν T : ℝ} {N : ℕ} (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hsmall : nativeProduct * ‖a‖ < ν) (hT : 0 ≤ T)
    (g : GalerkinSolution ν (finiteSynthesis N (criticalCoeff 1 a)) N),
    budget6 N g.coeff T ≤
      ENNReal.ofReal (‖a‖ ^ 4 / (4 * (ν - nativeProduct * ‖a‖))) :=
  @SingularClosure.H12Frontier.PRODUCT_SIX_CHANNEL_BUDGET

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.H12Frontier.PRODUCT_SIX_CHANNEL_BUDGET"
#print axioms SingularClosure.H12Frontier.PRODUCT_SIX_CHANNEL_BUDGET

example :
    ∀ (ν : ℝ) (_hν : 0 < ν) (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (_hsol : SpectralSolenoidal (criticalCoeff 1 a))
    (_hzero : SpectralMeanZero (criticalCoeff 1 a))
    (hsmall : nativeProduct * ‖a‖ < ν),
    CriticalDatumAX6 ν a :=
  @SingularClosure.H12Frontier.PRODUCT_DATUM_AX6

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.H12Frontier.PRODUCT_DATUM_AX6"
#print axioms SingularClosure.H12Frontier.PRODUCT_DATUM_AX6

end
end SingularClosure.H12Frontier
