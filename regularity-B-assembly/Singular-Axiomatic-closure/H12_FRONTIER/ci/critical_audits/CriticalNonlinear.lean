import SingularClosure.CriticalNonlinear

set_option autoImplicit false
set_option Elab.async false
open Set MeasureTheory Filter
open scoped BigOperators ContDiff Topology ENNReal Interval
namespace SingularClosure
noncomputable section

example :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∀ c : FourierCoeff,
      (∀ k : Frequency, k ∉ cutoffModes N → ∀ i : Fin 3, c k i = 0) →
      SpectralReality c → SpectralSolenoidal c →
      |criticalNonlinearPower 1 N c| ≤
        C * Real.sqrt (criticalEnergy 1 N c) * criticalEnergy 3 N c :=
  @SingularClosure.FINITE_CRITICAL_NONLINEAR_BOUND

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.FINITE_CRITICAL_NONLINEAR_BOUND"
#check @SingularClosure.FINITE_CRITICAL_NONLINEAR_BOUND
#print axioms SingularClosure.FINITE_CRITICAL_NONLINEAR_BOUND

end
end SingularClosure
