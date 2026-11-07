import Tail16Admission.Syntax

set_option autoImplicit false

open scoped BigOperators

namespace Tail16Admission

noncomputable section

/-- Total lookup used by literal semantics; well-scoped syntax never uses the default case. -/
def lookupNat : List Nat → Nat → Nat
  | [], _ => 0
  | x :: _, 0 => x
  | _ :: xs, i + 1 => lookupNat xs i

def denoteN (ρ : List Nat) : NExpr → Nat
  | .lit n    => n
  | .var i    => lookupNat ρ i
  | .succ t   => denoteN ρ t + 1
  | .add a b  => denoteN ρ a + denoteN ρ b
  | .mul a b  => denoteN ρ a * denoteN ρ b
  | .tsub a b => denoteN ρ a - denoteN ρ b

def denoteR (ρ : List Nat) : RExpr → ℝ
  | .rat z d =>
      (z : ℝ) / (d : ℝ)
  | .natCast t =>
      (denoteN ρ t : ℝ)
  | .u t =>
      RH_HilbertLimit.actualNormalizedMoment (denoteN ρ t)
  | .V t =>
      RH_HilbertLimit.actualVariation (denoteN ρ t)
  | .C t =>
      RH_HilbertLimit.rowCancellation
        RH_HilbertLimit.actualNormalizedMoment
        (denoteN ρ t)
  | .B n j =>
      RH_HilbertLimit.bernsteinWeight
        RH_HilbertLimit.actualNormalizedMoment
        (denoteN ρ n)
        (denoteN ρ j)
  | .D n j =>
      RH_HilbertLimit.cancellationDefect
        RH_HilbertLimit.actualNormalizedMoment
        (denoteN ρ n)
        (denoteN ρ j)
  | .neg a =>
      - denoteR ρ a
  | .add a b =>
      denoteR ρ a + denoteR ρ b
  | .mul a b =>
      denoteR ρ a * denoteR ρ b
  | .pow a n =>
      denoteR ρ a ^ n
  | .abs a =>
      |denoteR ρ a|
  | .sum bound body =>
      ∑ j ∈ Finset.range (denoteN ρ bound), denoteR (j :: ρ) body

def Holds (ρ : List Nat) : Formula → Prop
  | .top      => True
  | .bot      => False
  | .nEq a b  => denoteN ρ a = denoteN ρ b
  | .nLe a b  => denoteN ρ a ≤ denoteN ρ b
  | .rEq a b  => denoteR ρ a = denoteR ρ b
  | .rLe a b  => denoteR ρ a ≤ denoteR ρ b
  | .conj A B => Holds ρ A ∧ Holds ρ B
  | .impl A B => Holds ρ A → Holds ρ B
  | .all A    => ∀ n : Nat, Holds (n :: ρ) A

/-- The literal semantic target corresponding to `budgetFormula`. -/
def BudgetSemantics (Y : Nat) : Prop :=
  ∀ n : Nat,
    16 ≤ n →
    RH_HilbertLimit.rowCancellation
        RH_HilbertLimit.actualNormalizedMoment n
      ≤
    (Y : ℝ) * RH_HilbertLimit.actualVariation n

theorem budgetFormula_semantics (Y : Nat) :
    Holds [] (budgetFormula Y) ↔ BudgetSemantics Y := by
  rfl

/-- Exact identification with the existing actual-ξ cancellation-budget proposition. -/
theorem budgetFormula_iff_admissible (Y : Nat) :
    Holds [] (budgetFormula Y) ↔
      (RHFrozenWitness.budget16 Y).Admissible := by
  rfl

#check lookupNat
#check denoteN
#check denoteR
#check Holds
#check BudgetSemantics
#check budgetFormula_semantics
#check budgetFormula_iff_admissible

#print axioms Tail16Admission.budgetFormula_semantics
#print axioms Tail16Admission.budgetFormula_iff_admissible

end

end Tail16Admission
