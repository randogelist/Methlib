import Tail16Admission.Semantics
import Tail16Frontier.BoolFacts

set_option autoImplicit false

namespace Tail16Admission

/-- Environments agree on the indices admitted by a scope. -/
def EnvAgree (k : Nat) (rho tau : List Nat) : Prop :=
  ∀ i : Nat, i < k → lookupNat rho i = lookupNat tau i

theorem envAgree_cons {k : Nat} {rho tau : List Nat}
    (h : EnvAgree k rho tau) (n : Nat) :
    EnvAgree (k + 1) (n :: rho) (n :: tau) := by
  intro i hi
  cases i with
  | zero => rfl
  | succ i =>
      exact h i (Nat.lt_of_succ_lt_succ hi)

theorem denoteN_agree {k : Nat} (a : NExpr) {rho tau : List Nat}
    (hs : a.wellScoped k = true) (ha : EnvAgree k rho tau) :
    denoteN rho a = denoteN tau a := by
  induction a with
  | lit n => rfl
  | var i =>
      exact ha i (by simpa [NExpr.wellScoped] using hs)
  | succ a ih =>
      have hsa : a.wellScoped k = true := hs
      simp only [denoteN, ih hsa]
  | add a b iha ihb =>
      have hab : a.wellScoped k = true ∧ b.wellScoped k = true :=
        Tail16Bool.andTrue hs
      simp only [denoteN, iha hab.1, ihb hab.2]
  | mul a b iha ihb =>
      have hab : a.wellScoped k = true ∧ b.wellScoped k = true :=
        Tail16Bool.andTrue hs
      simp only [denoteN, iha hab.1, ihb hab.2]
  | tsub a b iha ihb =>
      have hab : a.wellScoped k = true ∧ b.wellScoped k = true :=
        Tail16Bool.andTrue hs
      simp only [denoteN, iha hab.1, ihb hab.2]

theorem denoteR_agree {k : Nat} (a : RExpr) {rho tau : List Nat}
    (hs : a.wellScoped k = true) (ha : EnvAgree k rho tau) :
    denoteR rho a = denoteR tau a := by
  induction a generalizing k rho tau with
  | rat z d => rfl
  | natCast t =>
      simp only [denoteR, denoteN_agree t hs ha]
  | u t =>
      simp only [denoteR, denoteN_agree t hs ha]
  | V t =>
      simp only [denoteR, denoteN_agree t hs ha]
  | C t =>
      simp only [denoteR, denoteN_agree t hs ha]
  | B n j =>
      have hnj : n.wellScoped k = true ∧ j.wellScoped k = true :=
        Tail16Bool.andTrue hs
      simp only [denoteR, denoteN_agree n hnj.1 ha,
        denoteN_agree j hnj.2 ha]
  | D n j =>
      have hnj : n.wellScoped k = true ∧ j.wellScoped k = true :=
        Tail16Bool.andTrue hs
      simp only [denoteR, denoteN_agree n hnj.1 ha,
        denoteN_agree j hnj.2 ha]
  | neg a ih =>
      simp only [denoteR, ih hs ha]
  | add a b iha ihb =>
      have hab : a.wellScoped k = true ∧ b.wellScoped k = true :=
        Tail16Bool.andTrue hs
      simp only [denoteR, iha hab.1 ha, ihb hab.2 ha]
  | mul a b iha ihb =>
      have hab : a.wellScoped k = true ∧ b.wellScoped k = true :=
        Tail16Bool.andTrue hs
      simp only [denoteR, iha hab.1 ha, ihb hab.2 ha]
  | pow a n ih =>
      simp only [denoteR, ih hs ha]
  | abs a ih =>
      simp only [denoteR, ih hs ha]
  | sum bound body ih =>
      have hab : bound.wellScoped k = true ∧ body.wellScoped (k+1) = true :=
        Tail16Bool.andTrue hs
      simp only [denoteR]
      rw [denoteN_agree bound hab.1 ha]
      apply Finset.sum_congr rfl
      intro j hj
      exact ih hab.2 (envAgree_cons ha j)

theorem holds_agree {k : Nat} (F : Formula) {rho tau : List Nat}
    (hs : F.wellScoped k = true) (ha : EnvAgree k rho tau) :
    Holds rho F ↔ Holds tau F := by
  induction F generalizing k rho tau with
  | top => rfl
  | bot => rfl
  | nEq a b =>
      have hab : a.wellScoped k = true ∧ b.wellScoped k = true :=
        Tail16Bool.andTrue hs
      simp only [Holds, denoteN_agree a hab.1 ha, denoteN_agree b hab.2 ha]
  | nLe a b =>
      have hab : a.wellScoped k = true ∧ b.wellScoped k = true :=
        Tail16Bool.andTrue hs
      simp only [Holds, denoteN_agree a hab.1 ha, denoteN_agree b hab.2 ha]
  | rEq a b =>
      have hab : a.wellScoped k = true ∧ b.wellScoped k = true :=
        Tail16Bool.andTrue hs
      simp only [Holds, denoteR_agree a hab.1 ha, denoteR_agree b hab.2 ha]
  | rLe a b =>
      have hab : a.wellScoped k = true ∧ b.wellScoped k = true :=
        Tail16Bool.andTrue hs
      simp only [Holds, denoteR_agree a hab.1 ha, denoteR_agree b hab.2 ha]
  | conj A B ihA ihB =>
      have hab : A.wellScoped k = true ∧ B.wellScoped k = true :=
        Tail16Bool.andTrue hs
      simp only [Holds, ihA hab.1 ha, ihB hab.2 ha]
  | impl A B ihA ihB =>
      have hab : A.wellScoped k = true ∧ B.wellScoped k = true :=
        Tail16Bool.andTrue hs
      simp only [Holds, ihA hab.1 ha, ihB hab.2 ha]
  | all P ih =>
      change (∀ n : Nat, Holds (n :: rho) P) ↔
        (∀ n : Nat, Holds (n :: tau) P)
      constructor
      · intro h n
        exact (ih hs (envAgree_cons ha n)).1 (h n)
      · intro h n
        exact (ih hs (envAgree_cons ha n)).2 (h n)

theorem holds_closed (F : Formula) (hF : F.wellScoped 0 = true)
    (rho : List Nat) : Holds rho F ↔ Holds [] F := by
  apply holds_agree F hF
  intro i hi
  simp at hi

theorem holds_trim_one (P : Formula) (hP : P.wellScoped 1 = true)
    (n m : Nat) : Holds [n,m] P ↔ Holds [n] P := by
  apply holds_agree P hP
  intro i hi
  cases i with
  | zero => rfl
  | succ i => simp at hi

end Tail16Admission
