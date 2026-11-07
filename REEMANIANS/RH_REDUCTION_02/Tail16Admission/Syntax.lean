import RHFrozenWitnessArchitecture

set_option autoImplicit false

namespace Tail16Admission

/-- Finite natural-number expressions with de Bruijn-style variable indices. -/
inductive NExpr where
  | lit  : Nat → NExpr
  | var  : Nat → NExpr
  | succ : NExpr → NExpr
  | add  : NExpr → NExpr → NExpr
  | mul  : NExpr → NExpr → NExpr
  | tsub : NExpr → NExpr → NExpr
deriving Repr, DecidableEq

/--
Finite real expressions.

`u`, `V`, and `C` are frozen actual-ξ symbols:
  u(n) = actualNormalizedMoment n
  V(n) = actualVariation n
  C(n) = rowCancellation actualNormalizedMoment n

`B` and `D` expose the fixed Bernstein-weight and cancellation-defect
symbols needed by later primitive rules.

In `sum bound body`, variable 0 of `body` is the summation index and
all outer variables are shifted by one.
-/
inductive RExpr where
  | rat     : Int → Nat → RExpr
  | natCast : NExpr → RExpr
  | u       : NExpr → RExpr
  | V       : NExpr → RExpr
  | C       : NExpr → RExpr
  | B       : NExpr → NExpr → RExpr
  | D       : NExpr → NExpr → RExpr
  | neg     : RExpr → RExpr
  | add     : RExpr → RExpr → RExpr
  | mul     : RExpr → RExpr → RExpr
  | pow     : RExpr → Nat → RExpr
  | abs     : RExpr → RExpr
  | sum     : NExpr → RExpr → RExpr
deriving Repr, DecidableEq

/-- Finite proposition language accepted by the restricted checker. -/
inductive Formula where
  | top  : Formula
  | bot  : Formula
  | nEq  : NExpr → NExpr → Formula
  | nLe  : NExpr → NExpr → Formula
  | rEq  : RExpr → RExpr → Formula
  | rLe  : RExpr → RExpr → Formula
  | conj : Formula → Formula → Formula
  | impl : Formula → Formula → Formula
  | all  : Formula → Formula
deriving Repr, DecidableEq

namespace NExpr

/-- Explicit finite scope check. `k` is the number of available Nat variables. -/
def wellScoped (k : Nat) : NExpr → Bool
  | .lit _    => true
  | .var i    => decide (i < k)
  | .succ t   => wellScoped k t
  | .add a b  => wellScoped k a && wellScoped k b
  | .mul a b  => wellScoped k a && wellScoped k b
  | .tsub a b => wellScoped k a && wellScoped k b

end NExpr

namespace RExpr

/-- Scope check plus the finite nonzero-denominator check for rational literals. -/
def wellScoped (k : Nat) : RExpr → Bool
  | .rat _ d     => decide (d ≠ 0)
  | .natCast t   => t.wellScoped k
  | .u t         => t.wellScoped k
  | .V t         => t.wellScoped k
  | .C t         => t.wellScoped k
  | .B n j       => n.wellScoped k && j.wellScoped k
  | .D n j       => n.wellScoped k && j.wellScoped k
  | .neg a       => wellScoped k a
  | .add a b     => wellScoped k a && wellScoped k b
  | .mul a b     => wellScoped k a && wellScoped k b
  | .pow a _     => wellScoped k a
  | .abs a       => wellScoped k a
  | .sum bound a => bound.wellScoped k && wellScoped (k + 1) a

end RExpr

namespace Formula

def wellScoped (k : Nat) : Formula → Bool
  | .top        => true
  | .bot        => true
  | .nEq a b    => a.wellScoped k && b.wellScoped k
  | .nLe a b    => a.wellScoped k && b.wellScoped k
  | .rEq a b    => a.wellScoped k && b.wellScoped k
  | .rLe a b    => a.wellScoped k && b.wellScoped k
  | .conj A B   => wellScoped k A && wellScoped k B
  | .impl A B   => wellScoped k A && wellScoped k B
  | .all A      => wellScoped (k + 1) A

end Formula

/--
The exact frozen Tail16 cancellation-budget formula.

Under the literal semantics:
  ∀ n, 16 ≤ n →
    rowCancellation actualNormalizedMoment n ≤
      Y * actualVariation n.
-/
def budgetFormula (Y : Nat) : Formula :=
  .all (
    .impl
      (.nLe (.lit 16) (.var 0))
      (.rLe
        (.C (.var 0))
        (.mul (.natCast (.lit Y)) (.V (.var 0))))
  )

theorem budgetFormula_wellScoped (Y : Nat) :
    (budgetFormula Y).wellScoped 0 = true := by
  simp [budgetFormula, Formula.wellScoped, RExpr.wellScoped, NExpr.wellScoped]

#check NExpr
#check RExpr
#check Formula
#check NExpr.wellScoped
#check RExpr.wellScoped
#check Formula.wellScoped
#check budgetFormula
#check budgetFormula_wellScoped

#print axioms Tail16Admission.budgetFormula_wellScoped

end Tail16Admission
