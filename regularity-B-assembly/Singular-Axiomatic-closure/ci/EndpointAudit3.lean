import SingularClosure.GalerkinGlobal

set_option autoImplicit false
set_option Elab.async false
open Set MeasureTheory SingularClosure
open scoped Interval

noncomputable section

example : ∀ (ν : ℝ) (hν : 0 < ν)
    (a : Field) (ha : SmoothSigmaZero a) (N : ℕ),
    ∃ g : GalerkinSolution ν a N, ∀ h : GalerkinSolution ν a N,
      EqOn g.coeff h.coeff (Ici 0) :=
  @SingularClosure.GALERKIN_GLOBAL_EXISTS_UNIQUE

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.GALERKIN_GLOBAL_EXISTS_UNIQUE"
#check @SingularClosure.GALERKIN_GLOBAL_EXISTS_UNIQUE
#print axioms SingularClosure.GALERKIN_GLOBAL_EXISTS_UNIQUE

end
