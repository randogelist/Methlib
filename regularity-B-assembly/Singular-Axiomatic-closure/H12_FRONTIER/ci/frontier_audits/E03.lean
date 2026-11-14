import SingularClosure.H12Frontier.NonlinearBound

/-! Concrete specialization; every nonlinear certificate is constructed from
proved physical inequalities. All registered datum hypotheses are retained. -/
set_option autoImplicit false
set_option Elab.async false
open Set MeasureTheory Filter
open scoped BigOperators Topology Interval NNReal ENNReal
namespace SingularClosure.H12Frontier
noncomputable section

example :
    ∀ (N : ℕ) (c : FourierCoeff)
    (hsupp : ∀ k : Frequency, k ∉ cutoffModes N → ∀ i : Fin 3, c k i = 0)
    (hreal : SpectralReality c) (hsol : SpectralSolenoidal c),
    |criticalNonlinearPower 1 N c| ≤
      frontierConstant * Real.sqrt (criticalEnergy 1 N c) * criticalEnergy 3 N c :=
  @SingularClosure.H12Frontier.FRONTIER_FINITE_CRITICAL_NONLINEAR_BOUND

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.H12Frontier.FRONTIER_FINITE_CRITICAL_NONLINEAR_BOUND"
#print axioms SingularClosure.H12Frontier.FRONTIER_FINITE_CRITICAL_NONLINEAR_BOUND

end
end SingularClosure.H12Frontier
