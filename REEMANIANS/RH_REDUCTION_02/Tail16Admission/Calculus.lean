import Tail16Admission.ActualPrimitives

set_option autoImplicit false

namespace Tail16Admission

/-- Binder-free fragment used by the first universal/induction checker. -/
def RExpr.binderFree : RExpr → Bool
  | .rat _ _     => true
  | .natCast _   => true
  | .u _         => true
  | .V _         => true
  | .C _         => true
  | .B _ _       => true
  | .D _ _       => true
  | .neg a       => a.binderFree
  | .add a b     => a.binderFree && b.binderFree
  | .mul a b     => a.binderFree && b.binderFree
  | .pow a _     => a.binderFree
  | .abs a       => a.binderFree
  | .sum _ _     => false

def Formula.binderFree : Formula → Bool
  | .top        => true
  | .bot        => true
  | .nEq _ _    => true
  | .nLe _ _    => true
  | .rEq a b    => a.binderFree && b.binderFree
  | .rLe a b    => a.binderFree && b.binderFree
  | .conj A B   => A.binderFree && B.binderFree
  | .impl A B   => A.binderFree && B.binderFree
  | .all _      => false

/--
Substitute the leading Nat variable and lower all remaining indices by one.
Arguments are explicit: the replacement is first, the expression traversed second.
-/
def NExpr.subst0 (t : NExpr) : NExpr → NExpr
  | .lit n    => .lit n
  | .var 0    => t
  | .var (i+1) => .var i
  | .succ a   => .succ (NExpr.subst0 t a)
  | .add a b  => .add (NExpr.subst0 t a) (NExpr.subst0 t b)
  | .mul a b  => .mul (NExpr.subst0 t a) (NExpr.subst0 t b)
  | .tsub a b => .tsub (NExpr.subst0 t a) (NExpr.subst0 t b)

/-- Regression: a distinct literal source is retained. -/
theorem subst0_literal_control :
    NExpr.subst0 (.lit 7) (.lit 3) = .lit 3 := by
  rfl

/-- Regression: the leading variable is replaced, not the replacement traversed. -/
theorem subst0_var_zero_control :
    NExpr.subst0 (.lit 7) (.var 0) = .lit 7 := by
  rfl

/-- Regression: subsequent free-variable indices decrease by one. -/
theorem subst0_var_succ_control :
    NExpr.subst0 (.lit 7) (.var 3) = .var 2 := by
  rfl

/-- Regression: traversal descends through the source and leaves the replacement intact. -/
theorem subst0_compound_control :
    NExpr.subst0 (.add (.lit 7) (.var 0))
      (.mul (.succ (.var 0)) (.var 2)) =
    .mul (.succ (.add (.lit 7) (.var 0))) (.var 1) := by
  rfl

def RExpr.subst0 (t : NExpr) : RExpr → RExpr
  | .rat z d     => .rat z d
  | .natCast a   => .natCast (NExpr.subst0 t a)
  | .u a         => .u (NExpr.subst0 t a)
  | .V a         => .V (NExpr.subst0 t a)
  | .C a         => .C (NExpr.subst0 t a)
  | .B a b       => .B (NExpr.subst0 t a) (NExpr.subst0 t b)
  | .D a b       => .D (NExpr.subst0 t a) (NExpr.subst0 t b)
  | .neg a       => .neg (RExpr.subst0 t a)
  | .add a b     => .add (RExpr.subst0 t a) (RExpr.subst0 t b)
  | .mul a b     => .mul (RExpr.subst0 t a) (RExpr.subst0 t b)
  | .pow a n     => .pow (RExpr.subst0 t a) n
  | .abs a       => .abs (RExpr.subst0 t a)
  | .sum b a     => .sum (NExpr.subst0 t b) a

def Formula.subst0 (t : NExpr) : Formula → Formula
  | .top        => .top
  | .bot        => .bot
  | .nEq a b    => .nEq (NExpr.subst0 t a) (NExpr.subst0 t b)
  | .nLe a b    => .nLe (NExpr.subst0 t a) (NExpr.subst0 t b)
  | .rEq a b    => .rEq (RExpr.subst0 t a) (RExpr.subst0 t b)
  | .rLe a b    => .rLe (RExpr.subst0 t a) (RExpr.subst0 t b)
  | .conj A B   => .conj (Formula.subst0 t A) (Formula.subst0 t B)
  | .impl A B   => .impl (Formula.subst0 t A) (Formula.subst0 t B)
  | .all A      => .all A

theorem denoteN_subst0
    (ρ : List Nat) (t a : NExpr) :
    denoteN ρ (NExpr.subst0 t a) =
      denoteN (denoteN ρ t :: ρ) a := by
  induction a with
  | lit n => rfl
  | var i =>
      cases i with
      | zero => rfl
      | succ i => rfl
  | succ a ih =>
      simp [NExpr.subst0, denoteN, ih]
  | add a b iha ihb =>
      simp [NExpr.subst0, denoteN, iha, ihb]
  | mul a b iha ihb =>
      simp [NExpr.subst0, denoteN, iha, ihb]
  | tsub a b iha ihb =>
      simp [NExpr.subst0, denoteN, iha, ihb]

theorem denoteR_subst0_of_binderFree
    (ρ : List Nat) (t : NExpr) (a : RExpr)
    (hfree : a.binderFree = true) :
    denoteR ρ (RExpr.subst0 t a) =
      denoteR (denoteN ρ t :: ρ) a := by
  induction a with
  | rat z d => rfl
  | natCast a => simp [RExpr.subst0, denoteR, denoteN_subst0]
  | u a => simp [RExpr.subst0, denoteR, denoteN_subst0]
  | V a => simp [RExpr.subst0, denoteR, denoteN_subst0]
  | C a => simp [RExpr.subst0, denoteR, denoteN_subst0]
  | B a b => simp [RExpr.subst0, denoteR, denoteN_subst0]
  | D a b => simp [RExpr.subst0, denoteR, denoteN_subst0]
  | neg a ih =>
      simp [RExpr.binderFree] at hfree
      simp [RExpr.subst0, denoteR, ih hfree]
  | add a b iha ihb =>
      simp [RExpr.binderFree] at hfree
      rcases hfree with ⟨ha, hb⟩
      simp [RExpr.subst0, denoteR, iha ha, ihb hb]
  | mul a b iha ihb =>
      simp [RExpr.binderFree] at hfree
      rcases hfree with ⟨ha, hb⟩
      simp [RExpr.subst0, denoteR, iha ha, ihb hb]
  | pow a n ih =>
      simp [RExpr.binderFree] at hfree
      simp [RExpr.subst0, denoteR, ih hfree]
  | abs a ih =>
      simp [RExpr.binderFree] at hfree
      simp [RExpr.subst0, denoteR, ih hfree]
  | sum b a ih =>
      simp [RExpr.binderFree] at hfree

theorem holds_subst0_of_binderFree
    (ρ : List Nat) (t : NExpr) (F : Formula)
    (hfree : F.binderFree = true) :
    Holds ρ (Formula.subst0 t F) ↔
      Holds (denoteN ρ t :: ρ) F := by
  induction F with
  | top => rfl
  | bot => rfl
  | nEq a b =>
      simp [Formula.subst0, Holds, denoteN_subst0]
  | nLe a b =>
      simp [Formula.subst0, Holds, denoteN_subst0]
  | rEq a b =>
      simp [Formula.binderFree] at hfree
      rcases hfree with ⟨ha, hb⟩
      simp [Formula.subst0, Holds,
        denoteR_subst0_of_binderFree ρ t a ha,
        denoteR_subst0_of_binderFree ρ t b hb]
  | rLe a b =>
      simp [Formula.binderFree] at hfree
      rcases hfree with ⟨ha, hb⟩
      simp [Formula.subst0, Holds,
        denoteR_subst0_of_binderFree ρ t a ha,
        denoteR_subst0_of_binderFree ρ t b hb]
  | conj A B ihA ihB =>
      simp [Formula.binderFree] at hfree
      rcases hfree with ⟨hA, hB⟩
      simp [Formula.subst0, Holds, ihA hA, ihB hB]
  | impl A B ihA ihB =>
      simp [Formula.binderFree] at hfree
      rcases hfree with ⟨hA, hB⟩
      simp [Formula.subst0, Holds, ihA hA, ihB hB]
  | all A ih =>
      simp [Formula.binderFree] at hfree

/-- Finite restricted proof-tree syntax. -/
inductive Proof where
  | hyp      : Nat → Proof
  | triv     : Proof
  | andI     : Proof → Proof → Proof
  | andEL    : Proof → Proof
  | andER    : Proof → Proof
  | impI     : Formula → Proof → Proof
  | impE     : Proof → Proof → Proof
  | falseE   : Formula → Proof → Proof
  | allI     : Proof → Proof
  | allE     : NExpr → Proof → Proof
  | natInd   : Formula → Proof → Proof → Proof
  | prim     : ActualPrimitive → Proof
deriving Repr


/-- Lean-4.33-compatible finite context lookup. -/
def formulaAt? : List Formula → Nat → Option Formula
  | [], _ => none
  | A :: _, 0 => some A
  | _ :: Γ, i + 1 => formulaAt? Γ i

/--
Deterministic inference for the first restricted calculus.

Universal introduction and induction are deliberately restricted to the
empty outer context and arity zero. Induction and universal elimination
require binder-free bodies; universal introduction requires scope only.
This is sufficient for the frozen one-quantifier Tail16 root and keeps the
first checker kernel small.
-/
def infer : Nat → List Formula → Proof → Option Formula
  | k, _, .prim p => if p.check k then some p.conclusion else none
  | k, Γ, .hyp i => formulaAt? Γ i
  | _, _, .triv => some .top
  | k, Γ, .andI p q =>
      match infer k Γ p, infer k Γ q with
      | some A, some B => some (.conj A B)
      | _, _ => none
  | k, Γ, .andEL p =>
      match infer k Γ p with
      | some (.conj A _) => some A
      | _ => none
  | k, Γ, .andER p =>
      match infer k Γ p with
      | some (.conj _ B) => some B
      | _ => none
  | k, Γ, .impI A p =>
      if A.wellScoped k then
        match infer k (A :: Γ) p with
        | some B => some (.impl A B)
        | none => none
      else none
  | k, Γ, .impE p q =>
      match infer k Γ p, infer k Γ q with
      | some (.impl A B), some A' =>
          if A' = A then some B else none
      | _, _ => none
  | k, Γ, .falseE target p =>
      if target.wellScoped k then
        match infer k Γ p with
        | some .bot => some target
        | _ => none
      else none
  | k, Γ, .allI p =>
      if hk : k = 0 then
        if hΓ : Γ = [] then
          match infer 1 [] p with
          | some F =>
              if F.wellScoped 1 then some (.all F) else none
          | none => none
        else none
      else none
  | k, Γ, .allE t p =>
      if ht : t.wellScoped k then
        match infer k Γ p with
        | some (.all F) =>
            if hf : F.binderFree then some (Formula.subst0 t F) else none
        | _ => none
      else none
  | k, Γ, .natInd P base step =>
      if hk : k = 0 then
        if hΓ : Γ = [] then
          if hs : P.wellScoped 1 then
            if hf : P.binderFree then
              let P0 := Formula.subst0 (.lit 0) P
              let PS := Formula.subst0 (.succ (.var 0)) P
              match infer 0 [] base, infer 1 [P] step with
              | some A, some B =>
                  if A = P0 ∧ B = PS then some (.all P) else none
              | _, _ => none
            else none
          else none
        else none
      else none

def checkProof (k : Nat) (Γ : List Formula) (p : Proof) (F : Formula) : Bool :=
  decide (infer k Γ p = some F)

#check RExpr.binderFree
#check Formula.binderFree
#check NExpr.subst0
#check Formula.subst0
#check denoteN_subst0
#check holds_subst0_of_binderFree
#check Proof
#check infer
#check checkProof

#print axioms Tail16Admission.denoteN_subst0
#print axioms Tail16Admission.denoteR_subst0_of_binderFree
#print axioms Tail16Admission.holds_subst0_of_binderFree

end Tail16Admission
