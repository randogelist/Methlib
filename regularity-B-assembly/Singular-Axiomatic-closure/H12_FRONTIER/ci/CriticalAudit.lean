import SingularClosure.CriticalGalerkin

set_option autoImplicit false
set_option Elab.async false
open SingularClosure Set

noncomputable section

example : ∀ (ν : ℝ), 0 ≤ ν → ∀ c : FourierCoeff,
    SpectralReality c → SpectralSolenoidal c → ∀ N : ℕ,
    ∃ g : GalerkinSolution ν (finiteSynthesis N c) N,
      g.coeff 0 = cutoffCoeff N c ∧
        ∀ h : GalerkinSolution ν (finiteSynthesis N c) N,
          EqOn g.coeff h.coeff (Ici 0) :=
  @CRITICAL_GALERKIN_GLOBAL_EXISTS_UNIQUE

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.CRITICAL_GALERKIN_GLOBAL_EXISTS_UNIQUE"
#check @SingularClosure.CRITICAL_GALERKIN_GLOBAL_EXISTS_UNIQUE
#print axioms SingularClosure.CRITICAL_GALERKIN_GLOBAL_EXISTS_UNIQUE

end
