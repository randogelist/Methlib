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
    (∫ t in (0 : ℝ)..T, coefficientDissipation N (g.coeff t) ^ 2) ≤
      (‖a‖ ^ 4 - criticalEnergy 1 N (g.coeff T) ^ 2) /
        (4 * (ν - nativeProduct * ‖a‖)) :=
  @SingularClosure.H12Frontier.PRODUCT_GALERKIN_SHARP_QUARTIC

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.H12Frontier.PRODUCT_GALERKIN_SHARP_QUARTIC"
#print axioms SingularClosure.H12Frontier.PRODUCT_GALERKIN_SHARP_QUARTIC

example :
    ∀ {ν T : ℝ} {N : ℕ} (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hsmall : nativeProduct * ‖a‖ < ν) (hT : 0 ≤ T)
    (g : GalerkinSolution ν (finiteSynthesis N (criticalCoeff 1 a)) N),
    ∀ t ∈ Icc 0 T,
      criticalEnergy 1 N (g.coeff t) ^ 2 +
        4 * (ν - nativeProduct * ‖a‖) *
          (∫ s in (0 : ℝ)..t, criticalEnergy 2 N (g.coeff s) ^ 2) ≤
        criticalEnergy 1 N (g.coeff 0) ^ 2 :=
  @SingularClosure.H12Frontier.PRODUCT_GALERKIN_SQUARE_BUDGET

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.H12Frontier.PRODUCT_GALERKIN_SQUARE_BUDGET"
#print axioms SingularClosure.H12Frontier.PRODUCT_GALERKIN_SQUARE_BUDGET

end
end SingularClosure.H12Frontier
