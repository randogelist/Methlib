import SingularClosure.H12Frontier.ConstantNormalization

/-! E03 for the explicitly proved admissible literature constant instance. -/
set_option autoImplicit false
set_option Elab.async true
namespace SingularClosure.H12Frontier
noncomputable section

def frontierCertificate : NonlinearCertificate :=
  nativeProductCertificate.enlarge frontierConstant nativeProduct_le_frontierConstant

theorem FRONTIER_FINITE_CRITICAL_NONLINEAR_BOUND
    (N : ℕ) (c : FourierCoeff)
    (hsupp : ∀ k : Frequency, k ∉ cutoffModes N → ∀ i : Fin 3, c k i = 0)
    (hreal : SpectralReality c) (hsol : SpectralSolenoidal c) :
    |criticalNonlinearPower 1 N c| ≤
      frontierConstant * Real.sqrt (criticalEnergy 1 N c) * criticalEnergy 3 N c :=
  frontierCertificate.bound N c hsupp hreal hsol

end
end SingularClosure.H12Frontier
