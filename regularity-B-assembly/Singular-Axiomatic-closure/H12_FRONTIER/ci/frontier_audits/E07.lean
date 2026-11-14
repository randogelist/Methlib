import SingularClosure.H12Frontier.DerivativeMilestone

/-! Concrete specialization; every nonlinear certificate is constructed from
proved physical inequalities. All registered datum hypotheses are retained. -/
set_option autoImplicit false
set_option Elab.async false
open Set MeasureTheory Filter
open scoped BigOperators Topology Interval NNReal ENNReal
namespace SingularClosure.H12Frontier
noncomputable section

example :
    ∀ {ν T : ℝ} {N : ℕ} (hν : 0 ≤ ν) (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hsmall : frontierConstant * ‖a‖ < ν) (hT : 0 ≤ T)
    (g : GalerkinSolution ν (finiteSynthesis N (criticalCoeff 1 a)) N),
    (∫ t in (0 : ℝ)..T, ‖g.criticalRhs (-1) t‖ ^ 2) ≤
      (ν + criticalTransportConstant * ‖a‖) ^ 2 * ‖a‖ ^ 2 /
        (2 * (ν - frontierConstant * ‖a‖)) :=
  @SingularClosure.H12Frontier.frontierTimeDerivativeBudget

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.H12Frontier.frontierTimeDerivativeBudget"
#print axioms SingularClosure.H12Frontier.frontierTimeDerivativeBudget

end
end SingularClosure.H12Frontier
