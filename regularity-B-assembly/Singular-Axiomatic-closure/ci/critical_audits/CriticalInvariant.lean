import SingularClosure.CriticalInvariant

set_option autoImplicit false
set_option Elab.async false
open Set MeasureTheory Filter
open scoped BigOperators ContDiff Topology ENNReal Interval
namespace SingularClosure
noncomputable section

example {A B d : ℝ → ℝ} {ν C a₀ T : ℝ}
    (hT : 0 ≤ T) (hC : 0 ≤ C) (ha₀ : 0 ≤ a₀)
    (hsmall : C * a₀ < ν)
    (hA : ContinuousOn A (Icc 0 T))
    (hB : ∀ t ∈ Ico 0 T, 0 ≤ B t)
    (hinit : A 0 ≤ a₀ ^ 2)
    (hderiv : ∀ t ∈ Ico 0 T, HasDerivWithinAt A (d t) (Ici 0) t)
    (hcritical : ∀ t ∈ Ico 0 T,
      d t + 2 * (ν - C * Real.sqrt (A t)) * B t ≤ 0) :
    ∀ t ∈ Icc 0 T, A t ≤ a₀ ^ 2 :=
  @SingularClosure.CRITICAL_ENERGY_INVARIANT A B d ν C a₀ T hT hC ha₀ hsmall hA hB hinit hderiv hcritical

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.CRITICAL_ENERGY_INVARIANT"
#check @SingularClosure.CRITICAL_ENERGY_INVARIANT
#print axioms SingularClosure.CRITICAL_ENERGY_INVARIANT

example {A B X d : ℝ → ℝ} {ν C a₀ T : ℝ}
    (hT : 0 ≤ T) (hC : 0 ≤ C) (ha₀ : 0 ≤ a₀)
    (hsmall : C * a₀ < ν)
    (hA : ContinuousOn A (Icc 0 T))
    (hX : ContinuousOn X (Icc 0 T))
    (hAnonneg : ∀ t ∈ Icc 0 T, 0 ≤ A t)
    (hB : ∀ t ∈ Ico 0 T, 0 ≤ B t)
    (hinit : A 0 ≤ a₀ ^ 2)
    (hderiv : ∀ t ∈ Ico 0 T, HasDerivWithinAt A (d t) (Ici 0) t)
    (hcritical : ∀ t ∈ Ico 0 T,
      d t + 2 * (ν - C * Real.sqrt (A t)) * B t ≤ 0)
    (hinterp : ∀ t ∈ Ioo 0 T, X t ^ 2 ≤ A t * B t) :
    (∫ s in (0 : ℝ)..T, X s ^ 2) ≤
      (a₀ ^ 4 - A T ^ 2) / (4 * (ν - C * a₀)) :=
  @SingularClosure.CRITICAL_SQUARE_BUDGET_DIV A B X d ν C a₀ T hT hC ha₀ hsmall hA hX hAnonneg hB hinit hderiv hcritical hinterp

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.CRITICAL_SQUARE_BUDGET_DIV"
#check @SingularClosure.CRITICAL_SQUARE_BUDGET_DIV
#print axioms SingularClosure.CRITICAL_SQUARE_BUDGET_DIV

end
end SingularClosure
