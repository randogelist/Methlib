import CondRecurrence
import CondTrace

namespace CondFeffA
open Fefferman Fefferman.ConcreteReal

noncomputable section

/-- The full spatial field of order-n right time derivatives of a velocity. -/
def timeJetField (s : Solution realAnalysis) (n : ℕ) : RInitial :=
  fun x i => rightJet (fun t => s.velocity x t i) n

/-- Evaluate the finite amplitude expansion before taking the first component
at the spatial origin. -/
def evalField (c : ℝ) (n : ℕ) : RInitial :=
  fun x i => jetTable n n 0 x i * c +
    ∑ k ∈ Finset.range n, jetTable n n (k+1) x i * c^(k+2)

theorem evalField_initial (c : ℝ) : evalField c 0 = datum c := by
  funext x i
  simp [evalField, jetTable, datum, mul_comm]

theorem evalField_sample (c : ℝ) (n : ℕ) : evalField c n 0 0 = (jetPolynomial n).eval c :=
  (jetPolynomial_eval n c).symm

/-- The projected equation differentiated n times, using unnormalized jets. -/
def nextTimeJet (n : ℕ) (J : ℕ → RInitial) : RInitial :=
  fun x i => heatStep (J n) x i -
    ∑ j ∈ Finset.range (n+1), (n.choose j : ℝ) * projectedTransport (J j) (J (n-j)) x i

theorem nextTimeJet_congr {n : ℕ} {J K : ℕ → RInitial}
    (h : ∀ j, j ≤ n → J j = K j) : nextTimeJet n J = nextTimeJet n K := by
  funext x i
  unfold nextTimeJet
  rw [h n le_rfl]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  rw [h j hj', h (n-j) (Nat.sub_le _ _)]

/-- Expansion of the heat and projected nonlinear operators on these
specific coefficient fields. This premise concerns explicit functions only. -/
def FiniteExpansionLaw (δ : ℝ) : Prop :=
  ∀ c ∈ Set.Ioo 0 δ, ∀ n, evalField c (n+1) = nextTimeJet n (evalField c)

/-- Physical differentiation and pressure projection for literal witnesses.
No canonical evolution needs to be chosen in this version. -/
def PhysicalProjectedRecurrence (δ : ℝ) : Prop :=
  ∀ c ∈ Set.Ioo 0 δ, ∀ s : Solution realAnalysis,
    globalSolution realAnalysis .wholeSpace unitViscosity (datum c) (zeroForce realAnalysis) s →
      ∀ n, timeJetField s (n+1) = nextTimeJet n (timeJetField s)

theorem witness_fields_eq_of_recurrences {δ c : ℝ} (hc : c ∈ Set.Ioo 0 δ)
    (s : Solution realAnalysis)
    (hs : globalSolution realAnalysis .wholeSpace unitViscosity (datum c) (zeroForce realAnalysis) s)
    (hphysical : PhysicalProjectedRecurrence δ) (hexpand : FiniteExpansionLaw δ) :
    ∀ n, timeJetField s n = evalField c n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero =>
      rw [evalField_initial]
      funext x i
      have htrace : clause03 realAnalysis (datum c) s := hs.2.2.1
      simpa [timeJetField, rightJet] using congrFun (htrace x) i
    | succ k =>
      rw [hphysical c hc s hs k, hexpand c hc k]
      apply nextTimeJet_congr
      intro j hj
      exact ih j (Nat.lt_succ_of_le hj)

end
end CondFeffA
