import SingularClosure.H12Frontier.PositiveMilestones

/-! Concrete specialization; every nonlinear certificate is constructed from
proved physical inequalities. All registered datum hypotheses are retained. -/
set_option autoImplicit false
set_option Elab.async false
open Set MeasureTheory Filter
open scoped BigOperators Topology Interval NNReal ENNReal
namespace SingularClosure.H12Frontier
noncomputable section

example :
    ∀ (ν : ℝ) (hν : 0 < ν) (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hsmall : frontierConstant * ‖a‖ < ν)
    (τ : ℝ) (hτ : 0 < τ) (T : ℝ) (hτT : τ ≤ T),
    ∃ L : ℝ, 0 ≤ L ∧ ∀ N : ℕ,
      ∀ g : GalerkinSolution ν (finiteSynthesis N (criticalCoeff 1 a)) N,
      ∀ t ∈ Icc τ T,
        coefficientDissipation N (g.coeff t) +
          ν * (∫ s in τ..t, coefficientLaplacianSquare N (g.coeff s)) ≤ L :=
  @SingularClosure.H12Frontier.frontierPositiveTimeEnstrophyAccumulation

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.H12Frontier.frontierPositiveTimeEnstrophyAccumulation"
#print axioms SingularClosure.H12Frontier.frontierPositiveTimeEnstrophyAccumulation

end
end SingularClosure.H12Frontier
