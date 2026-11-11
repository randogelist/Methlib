import SingularClosure.PhysicalEnergy

set_option autoImplicit false
set_option Elab.async false
open Set MeasureTheory SingularClosure
open scoped Interval

noncomputable section

example : ∀ {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N)
    {T : ℝ} (hT : 0 ≤ T),
    IntervalIntegrable (fun t => physicalDissipation (g.velocity t)) volume 0 T ∧
      physicalEnergy (g.velocity T) +
        2 * ν * (∫ t in (0 : ℝ)..T, physicalDissipation (g.velocity t)) =
          physicalEnergy (finiteSynthesis N (datumFourierCoeff a)) :=
  @SingularClosure.GALERKIN_ENERGY_IDENTITY

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.GALERKIN_ENERGY_IDENTITY"
#check @SingularClosure.GALERKIN_ENERGY_IDENTITY
#print axioms SingularClosure.GALERKIN_ENERGY_IDENTITY

end
