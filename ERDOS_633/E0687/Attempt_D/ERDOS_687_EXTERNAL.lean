/-!
Attempt_D external import. The OAI pinned Jacobsthal conclusion is used
only through its exact published types; no extra exponent is inferred
without the named UniformExactMargin premise.
Pin: openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
Lean: v4.34.1
-/
import ERDOS_687
import OAI.NumberTheory.Jacobsthal.Conclusions.QuadraticBound
import OAI.NumberTheory.Jacobsthal.Conclusions.IteratedLogBound

namespace Erdos687AttemptD

def ShiftCover (n m : ℕ) : Prop :=
  ∃ t : ℤ, ∀ i : ℕ, i < m →
    ¬ (t + (i : ℤ)).natAbs.Coprime n

/-- !! Uses the actual external Jacobsthal theorem signature. -/
theorem no_shift_cover_of_jacobsthal
    (k m n : ℕ)
    (h : OAI.Erdos970.NumberTheoryLean.Targets.IsJacobsthalBound k m)
    (hn : 0 < n) (hk : n.primeFactors.card ≤ k) :
    ¬ ShiftCover n m := by
  rintro ⟨t, hAll⟩
  obtain ⟨i, hi, hCoprime⟩ := h n hn hk t
  exact (hAll i hi) hCoprime

theorem external_quadratic :
    OAI.Erdos970.NumberTheoryLean.Targets.JacobsthalQuadratic :=
  OAI.Erdos970.Erdos970Final.erdos_970_quadratic

theorem external_iterated_log :
    OAI.Erdos970.NumberTheoryLean.Targets.JacobsthalIteratedLog :=
  OAI.Erdos970.Erdos970Final.erdos_970_iterated_log

/-- Conditional stronger result: the missing analytic premise is explicit. -/
theorem external_plus_exact_margin
    (hMargin : UniformExactMargin) :
    OAI.Erdos970.NumberTheoryLean.Targets.JacobsthalQuadratic ∧
      StrongNoCover := by
  exact ⟨external_quadratic, strong_of_exact_margin hMargin⟩

theorem external_improved_plus_short_budget
    (hCap : ResidueCountCap) (hBudget : UniformShortBudget) :
    OAI.Erdos970.NumberTheoryLean.Targets.JacobsthalIteratedLog ∧
      StrongNoCover := by
  exact ⟨external_iterated_log, strong_of_short_budget hCap hBudget⟩

#print axioms Erdos687AttemptD.no_shift_cover_of_jacobsthal
#print axioms Erdos687AttemptD.external_quadratic
#print axioms Erdos687AttemptD.external_iterated_log
#print axioms Erdos687AttemptD.external_plus_exact_margin
#print axioms Erdos687AttemptD.external_improved_plus_short_budget

end Erdos687AttemptD
