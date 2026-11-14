import SingularClosure.H12Frontier.ProductMilestones

set_option autoImplicit false
set_option Elab.async false
open Set MeasureTheory Filter
open scoped BigOperators Topology Interval NNReal ENNReal
namespace SingularClosure.H12Frontier
noncomputable section

example :
    ∀ {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N)
    {t : ℝ} (ht : 0 ≤ t),
    criticalEnergyRate ν 1 N (g.coeff t) +
      2 * (ν - nativeProduct * Real.sqrt (criticalEnergy 1 N (g.coeff t))) *
        criticalEnergy 3 N (g.coeff t) ≤ 0 :=
  @SingularClosure.H12Frontier.PRODUCT_GALERKIN_DIFFERENTIAL_INEQUALITY

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.H12Frontier.PRODUCT_GALERKIN_DIFFERENTIAL_INEQUALITY"
#print axioms SingularClosure.H12Frontier.PRODUCT_GALERKIN_DIFFERENTIAL_INEQUALITY

end
end SingularClosure.H12Frontier
