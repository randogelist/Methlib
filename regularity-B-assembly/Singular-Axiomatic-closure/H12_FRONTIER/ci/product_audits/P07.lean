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
    ∀ t ∈ Icc 0 T, criticalEnergy 1 N (g.coeff t) ≤ ‖a‖ ^ 2 :=
  @SingularClosure.H12Frontier.PRODUCT_GALERKIN_ENERGY_INVARIANT

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.H12Frontier.PRODUCT_GALERKIN_ENERGY_INVARIANT"
#print axioms SingularClosure.H12Frontier.PRODUCT_GALERKIN_ENERGY_INVARIANT

example :
    ∀ {ν T : ℝ} {N : ℕ} (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hsmall : nativeProduct * ‖a‖ < ν) (hT : 0 ≤ T)
    (g : GalerkinSolution ν (finiteSynthesis N (criticalCoeff 1 a)) N),
    ∀ t ∈ Icc 0 T,
      criticalEnergy 1 N (g.coeff t) + 2 * (ν - nativeProduct * ‖a‖) *
        (∫ s in (0 : ℝ)..t, criticalEnergy 3 N (g.coeff s)) ≤ ‖a‖ ^ 2 :=
  @SingularClosure.H12Frontier.PRODUCT_GALERKIN_DISSIPATION_BUDGET

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.H12Frontier.PRODUCT_GALERKIN_DISSIPATION_BUDGET"
#print axioms SingularClosure.H12Frontier.PRODUCT_GALERKIN_DISSIPATION_BUDGET

example :
    ∀ {ν : ℝ} {N : ℕ} (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hsmall : nativeProduct * ‖a‖ < ν)
    (g : GalerkinSolution ν (finiteSynthesis N (criticalCoeff 1 a)) N)
    {t : ℝ} (ht : 0 ≤ t),
    ‖g.criticalState 1 t‖ ≤ ‖a‖ :=
  @SingularClosure.H12Frontier.PRODUCT_GALERKIN_STATE_NORM_BOUND

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.H12Frontier.PRODUCT_GALERKIN_STATE_NORM_BOUND"
#print axioms SingularClosure.H12Frontier.PRODUCT_GALERKIN_STATE_NORM_BOUND

example :
    ∀ {ν T : ℝ} {N : ℕ} (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hsmall : nativeProduct * ‖a‖ < ν) (hT : 0 ≤ T)
    (g : GalerkinSolution ν (finiteSynthesis N (criticalCoeff 1 a)) N),
    (∫ t in (0 : ℝ)..T, ‖g.criticalState 3 t‖ ^ 2) ≤ (Replay.dissipationConstant nativeProductCertificate) ν a :=
  @SingularClosure.H12Frontier.PRODUCT_GALERKIN_STATE_THREE_INTEGRAL

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.H12Frontier.PRODUCT_GALERKIN_STATE_THREE_INTEGRAL"
#print axioms SingularClosure.H12Frontier.PRODUCT_GALERKIN_STATE_THREE_INTEGRAL

end
end SingularClosure.H12Frontier
