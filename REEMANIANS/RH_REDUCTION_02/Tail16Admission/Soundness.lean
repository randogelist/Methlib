import Tail16Admission.Calculus
import Tail16Frontier.ScopeAgreement

set_option autoImplicit false

namespace Tail16Admission

def Sat : List Formula → List Nat → Prop
  | [], _ => True
  | A :: Gamma, rho => Holds rho A ∧ Sat Gamma rho

theorem sat_empty (rho : List Nat) : Sat [] rho := trivial

theorem sat_cons {A : Formula} {Gamma : List Formula} {rho : List Nat}
    (hA : Holds rho A) (hGamma : Sat Gamma rho) : Sat (A :: Gamma) rho :=
  ⟨hA, hGamma⟩

theorem holds_of_formulaAt?_of_sat
    {Gamma : List Formula} {rho : List Nat} {i : Nat} {F : Formula}
    (hGamma : Sat Gamma rho)
    (hget : formulaAt? Gamma i = some F) : Holds rho F := by
  induction Gamma generalizing i with
  | nil => simp [formulaAt?] at hget
  | cons A Gamma ih =>
      rcases hGamma with ⟨hA, hGamma⟩
      cases i with
      | zero =>
          have hAF : A = F := by simpa [formulaAt?] using hget
          cases hAF
          exact hA
      | succ i =>
          exact ih hGamma (by simpa [formulaAt?] using hget)

/-- Fixed logical rules plus the independently proved fixed actual primitives. -/
theorem infer_sound
    {k : Nat} {Gamma : List Formula} {p : Proof} {F : Formula}
    (hinfer : infer k Gamma p = some F) :
    ∀ rho : List Nat, rho.length = k → Sat Gamma rho → Holds rho F := by
  induction p generalizing k Gamma F with
  | prim c =>
      intro rho hlen hsat
      by_cases hc : c.check k = true
      · have hF : c.conclusion = F := by simpa [infer, hc] using hinfer
        cases hF
        exact actualPrimitive_sound c hc rho hlen
      · simp [infer, hc] at hinfer
  | hyp i =>
      intro rho hlen hsat
      exact holds_of_formulaAt?_of_sat hsat (by simpa [infer] using hinfer)
  | triv =>
      intro rho hlen hsat
      have hF : Formula.top = F := by simpa [infer] using hinfer
      cases hF
      trivial
  | andI p q ihp ihq =>
      intro rho hlen hsat
      cases hp : infer k Gamma p with
      | none => simp [infer, hp] at hinfer
      | some A =>
          cases hq : infer k Gamma q with
          | none => simp [infer, hp, hq] at hinfer
          | some B =>
              have hF : Formula.conj A B = F := by
                simpa [infer, hp, hq] using hinfer
              cases hF
              exact ⟨ihp hp rho hlen hsat, ihq hq rho hlen hsat⟩
  | andEL p ih =>
      intro rho hlen hsat
      cases hp : infer k Gamma p with
      | none => simp [infer, hp] at hinfer
      | some G =>
          cases G with
          | top => simp [infer, hp] at hinfer
          | bot => simp [infer, hp] at hinfer
          | nEq a b => simp [infer, hp] at hinfer
          | nLe a b => simp [infer, hp] at hinfer
          | rEq a b => simp [infer, hp] at hinfer
          | rLe a b => simp [infer, hp] at hinfer
          | impl A B => simp [infer, hp] at hinfer
          | all A => simp [infer, hp] at hinfer
          | conj A B =>
              have hF : A = F := by simpa [infer, hp] using hinfer
              cases hF
              exact (ih hp rho hlen hsat).1
  | andER p ih =>
      intro rho hlen hsat
      cases hp : infer k Gamma p with
      | none => simp [infer, hp] at hinfer
      | some G =>
          cases G with
          | top => simp [infer, hp] at hinfer
          | bot => simp [infer, hp] at hinfer
          | nEq a b => simp [infer, hp] at hinfer
          | nLe a b => simp [infer, hp] at hinfer
          | rEq a b => simp [infer, hp] at hinfer
          | rLe a b => simp [infer, hp] at hinfer
          | impl A B => simp [infer, hp] at hinfer
          | all A => simp [infer, hp] at hinfer
          | conj A B =>
              have hF : B = F := by simpa [infer, hp] using hinfer
              cases hF
              exact (ih hp rho hlen hsat).2
  | impI A p ih =>
      intro rho hlen hsat
      by_cases hscope : A.wellScoped k = true
      · cases hp : infer k (A :: Gamma) p with
        | none => simp [infer, hscope, hp] at hinfer
        | some B =>
            have hF : Formula.impl A B = F := by
              simpa [infer, hscope, hp] using hinfer
            cases hF
            intro hA
            exact ih hp rho hlen (sat_cons hA hsat)
      · simp [infer, hscope] at hinfer
  | impE p q ihp ihq =>
      intro rho hlen hsat
      cases hp : infer k Gamma p with
      | none => simp [infer, hp] at hinfer
      | some G =>
          cases hq : infer k Gamma q with
          | none => simp [infer, hp, hq] at hinfer
          | some A' =>
              cases G with
              | top => simp [infer, hp, hq] at hinfer
              | bot => simp [infer, hp, hq] at hinfer
              | nEq a b => simp [infer, hp, hq] at hinfer
              | nLe a b => simp [infer, hp, hq] at hinfer
              | rEq a b => simp [infer, hp, hq] at hinfer
              | rLe a b => simp [infer, hp, hq] at hinfer
              | conj A B => simp [infer, hp, hq] at hinfer
              | all A => simp [infer, hp, hq] at hinfer
              | impl A B =>
                  by_cases heq : A' = A
                  · have hF : B = F := by
                      simpa [infer, hp, hq, heq] using hinfer
                    have hA : Holds rho A := by
                      simpa [heq] using (ihq hq rho hlen hsat)
                    cases hF
                    exact (ihp hp rho hlen hsat) hA
                  · simp [infer, hp, hq, heq] at hinfer
  | falseE target p ih =>
      intro rho hlen hsat
      by_cases hscope : target.wellScoped k = true
      · cases hp : infer k Gamma p with
        | none => simp [infer, hscope, hp] at hinfer
        | some G =>
            cases G with
            | top => simp [infer, hscope, hp] at hinfer
            | nEq a b => simp [infer, hscope, hp] at hinfer
            | nLe a b => simp [infer, hscope, hp] at hinfer
            | rEq a b => simp [infer, hscope, hp] at hinfer
            | rLe a b => simp [infer, hscope, hp] at hinfer
            | conj A B => simp [infer, hscope, hp] at hinfer
            | impl A B => simp [infer, hscope, hp] at hinfer
            | all A => simp [infer, hscope, hp] at hinfer
            | bot => exact False.elim (ih hp rho hlen hsat)
      · simp [infer, hscope] at hinfer
  | allI p ih =>
      intro rho hlen hsat
      by_cases hk : k = 0
      · rcases hk with rfl
        by_cases hGamma : Gamma = []
        · subst Gamma
          have hrho : rho = [] := by
            cases rho with
            | nil => rfl
            | cons x xs => simp at hlen
          subst rho
          cases hp : infer 1 [] p with
          | none => simp [infer, hp] at hinfer
          | some P =>
              by_cases hscope : P.wellScoped 1 = true
              · have hF : Formula.all P = F := by
                  simpa [infer, hp, hscope] using hinfer
                cases hF
                intro n
                exact ih hp [n] (by simp) trivial
              · simp [infer, hp, hscope] at hinfer
        · simp [infer, hGamma] at hinfer
      · simp [infer, hk] at hinfer
  | allE t p ih =>
      intro rho hlen hsat
      by_cases ht : t.wellScoped k = true
      · cases hp : infer k Gamma p with
        | none => simp [infer, ht, hp] at hinfer
        | some G =>
            cases G with
            | top => simp [infer, ht, hp] at hinfer
            | bot => simp [infer, ht, hp] at hinfer
            | nEq a b => simp [infer, ht, hp] at hinfer
            | nLe a b => simp [infer, ht, hp] at hinfer
            | rEq a b => simp [infer, ht, hp] at hinfer
            | rLe a b => simp [infer, ht, hp] at hinfer
            | conj A B => simp [infer, ht, hp] at hinfer
            | impl A B => simp [infer, ht, hp] at hinfer
            | all P =>
                by_cases hf : P.binderFree = true
                · have hF : P.subst0 t = F := by
                    simpa [infer, ht, hp, hf] using hinfer
                  cases hF
                  have hall : ∀ n : Nat, Holds (n :: rho) P :=
                    ih hp rho hlen hsat
                  exact (holds_subst0_of_binderFree rho t P hf).2
                    (hall (denoteN rho t))
                · simp [infer, ht, hp, hf] at hinfer
      · simp [infer, ht] at hinfer
  | natInd P base step ihBase ihStep =>
      intro rho hlen hsat
      by_cases hk : k = 0
      · rcases hk with rfl
        by_cases hGamma : Gamma = []
        · subst Gamma
          have hrho : rho = [] := by
            cases rho with
            | nil => rfl
            | cons x xs => simp at hlen
          subst rho
          by_cases hscope : P.wellScoped 1 = true
          · by_cases hfree : P.binderFree = true
            · cases hbase : infer 0 [] base with
              | none => simp [infer, hscope, hfree, hbase] at hinfer
              | some A =>
                  cases hstep : infer 1 [P] step with
                  | none => simp [infer, hscope, hfree, hbase, hstep] at hinfer
                  | some B =>
                      by_cases hAB :
                          A = P.subst0 (.lit 0) ∧
                          B = P.subst0 (.succ (.var 0))
                      · rcases hAB with ⟨hA, hB⟩
                        subst A
                        subst B
                        have hF : Formula.all P = F := by
                          simpa [infer, hscope, hfree, hbase, hstep] using hinfer
                        cases hF
                        intro n
                        induction n with
                        | zero =>
                            have hb : Holds [] (P.subst0 (.lit 0)) :=
                              ihBase hbase [] rfl trivial
                            exact
                              (holds_subst0_of_binderFree [] (.lit 0) P hfree).1 hb
                        | succ n ihn =>
                            have hs :
                                Holds [n] (P.subst0 (.succ (.var 0))) :=
                              ihStep hstep [n] (by simp) ⟨ihn, trivial⟩
                            have hs' : Holds [n+1,n] P :=
                              (holds_subst0_of_binderFree [n]
                                (.succ (.var 0)) P hfree).1 hs
                            exact (holds_trim_one P hscope (n+1) n).1 hs'
                      · simp [infer, hscope, hfree, hbase, hstep, hAB] at hinfer
            · simp [infer, hscope, hfree] at hinfer
          · simp [infer, hscope] at hinfer
        · simp [infer, hGamma] at hinfer
      · simp [infer, hk] at hinfer

theorem checkProof_sound {F : Formula} {p : Proof}
    (h : checkProof 0 [] p F = true) : Holds [] F := by
  have hinfer : infer 0 [] p = some F := by
    simpa [checkProof] using h
  exact infer_sound hinfer [] rfl trivial

end Tail16Admission

