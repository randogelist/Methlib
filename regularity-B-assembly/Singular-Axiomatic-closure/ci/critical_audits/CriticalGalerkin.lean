import SingularClosure.CriticalGalerkin

set_option autoImplicit false
set_option Elab.async false
open Set MeasureTheory Filter
open scoped BigOperators ContDiff Topology ENNReal Interval
namespace SingularClosure
noncomputable section

example (ν : ℝ) (hν : 0 ≤ ν) (c : FourierCoeff)
    (hreal : SpectralReality c) (hsol : SpectralSolenoidal c) (N : ℕ) :
    ∃ g : GalerkinSolution ν (finiteSynthesis N c) N,
      g.coeff 0 = cutoffCoeff N c ∧
        ∀ h : GalerkinSolution ν (finiteSynthesis N c) N,
          EqOn g.coeff h.coeff (Ici 0) :=
  @SingularClosure.CRITICAL_GALERKIN_GLOBAL_EXISTS_UNIQUE ν hν c hreal hsol N

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.CRITICAL_GALERKIN_GLOBAL_EXISTS_UNIQUE"
#check @SingularClosure.CRITICAL_GALERKIN_GLOBAL_EXISTS_UNIQUE
#print axioms SingularClosure.CRITICAL_GALERKIN_GLOBAL_EXISTS_UNIQUE

end
end SingularClosure
