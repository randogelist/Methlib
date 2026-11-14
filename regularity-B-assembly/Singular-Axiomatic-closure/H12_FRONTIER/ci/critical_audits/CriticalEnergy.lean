import SingularClosure.CriticalEnergy

set_option autoImplicit false
set_option Elab.async false
open Set MeasureTheory Filter
open scoped BigOperators ContDiff Topology ENNReal Interval
namespace SingularClosure
noncomputable section

example {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N)
    (q : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun r => criticalEnergy q N (g.coeff r))
      (criticalEnergyRate ν q N (g.coeff t)) (Ici 0) t :=
  @SingularClosure.GalerkinSolution.criticalEnergy_balance ν a N g q t ht

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.GalerkinSolution.criticalEnergy_balance"
#check @SingularClosure.GalerkinSolution.criticalEnergy_balance
#print axioms SingularClosure.GalerkinSolution.criticalEnergy_balance

end
end SingularClosure
