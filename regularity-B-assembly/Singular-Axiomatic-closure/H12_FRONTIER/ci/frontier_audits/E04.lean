import SingularClosure.H12Frontier.FiniteMilestones

/-! Concrete specialization; every nonlinear certificate is constructed from
proved physical inequalities. All registered datum hypotheses are retained. -/
set_option autoImplicit false
set_option Elab.async false
open Set MeasureTheory Filter
open scoped BigOperators Topology Interval NNReal ENNReal
namespace SingularClosure.H12Frontier
noncomputable section

example :
    ∀ {ν T : ℝ} {N : ℕ} (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hsmall : frontierConstant * ‖a‖ < ν) (hT : 0 ≤ T)
    (g : GalerkinSolution ν (finiteSynthesis N (criticalCoeff 1 a)) N),
    ∀ t ∈ Icc 0 T, criticalEnergy 1 N (g.coeff t) ≤ ‖a‖ ^ 2 :=
  @SingularClosure.H12Frontier.frontierGalerkinEnergyInvariant

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.H12Frontier.frontierGalerkinEnergyInvariant"
#print axioms SingularClosure.H12Frontier.frontierGalerkinEnergyInvariant

end
end SingularClosure.H12Frontier
