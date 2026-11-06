import FiniteAffine
import RankToCollatz

namespace PoincareSecond

set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

variable {d : ℕ}

def feature (W : Certificate d) (n : ℕ) : Vec d :=
  if hn : n < 2 then W.seed
  else if n % 2 = 0 then W.B0.eval (feature W (n / 2))
  else W.B1.eval (feature W (n / 2))
termination_by n
decreasing_by all_goals omega

@[simp] theorem feature_one (W : Certificate d) : feature W 1 = W.seed := by
  rw [feature]
  norm_num

theorem feature_even (W : Certificate d) (m : ℕ) (hm : 0 < m) :
    feature W (2 * m) = W.B0.eval (feature W m) := by
  rw [feature]
  have hn : ¬ 2 * m < 2 := by omega
  have hp : (2 * m) % 2 = 0 := by omega
  have hd : (2 * m) / 2 = m := by omega
  simp [hn, hp, hd]

theorem feature_odd (W : Certificate d) (m : ℕ) (hm : 0 < m) :
    feature W (2 * m + 1) = W.B1.eval (feature W m) := by
  rw [feature]
  have hn : ¬ 2 * m + 1 < 2 := by omega
  have hd : (2 * m + 1) / 2 = m := by omega
  simp [hn, hd]

@[simp] theorem feature_two (W : Certificate d) :
    feature W 2 = W.B0.eval W.seed := by
  simpa using feature_even W 1 (by omega)

@[simp] theorem feature_three (W : Certificate d) :
    feature W 3 = W.B1.eval W.seed := by
  simpa using feature_odd W 1 (by omega)

@[simp] theorem feature_four (W : Certificate d) :
    feature W 4 = W.B0.eval (W.B0.eval W.seed) := by
  simpa using feature_even W 2 (by omega)

@[simp] theorem feature_five (W : Certificate d) :
    feature W 5 = W.B1.eval (W.B0.eval W.seed) := by
  simpa using feature_odd W 2 (by omega)

theorem feature_nonneg (W : Certificate d) (h : W.Semantics) (n : ℕ) :
    0 ≤ feature W n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [feature]
    split
    · exact h.seed_nonneg
    · split
      · apply h.B0_nonneg
        exact ih (n / 2) (by omega)
      · apply h.B1_nonneg
        exact ih (n / 2) (by omega)

theorem arithmetic_adapter (W : Certificate d) (h : W.Semantics)
    (n : ℕ) (hn : 0 < n) :
    feature W (3 * n) ≤ W.G0.eval (feature W n) ∧
    feature W (3 * n + 1) ≤ W.G1.eval (feature W n) ∧
    feature W (3 * n + 2) ≤ W.G2.eval (feature W n) := by
  revert hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    by_cases hone : n = 1
    · subst n
      simpa using And.intro h.base0 (And.intro h.base1 h.base2)
    · by_cases hp : n % 2 = 0
      · obtain ⟨m, hmform⟩ : ∃ m : ℕ, n = 2 * m := ⟨n / 2, by omega⟩
        subst n
        have hm : 0 < m := by omega
        have hlt : m < 2 * m := by omega
        obtain ⟨hi0, hi1, hi2⟩ := ih m hlt hm
        have hnn := feature_nonneg W h m
        refine ⟨?_, ?_, ?_⟩
        · calc
            feature W (3 * (2 * m)) = W.B0.eval (feature W (3 * m)) := by
              rw [show 3 * (2 * m) = 2 * (3 * m) by omega]
              exact feature_even W (3 * m) (by omega)
            _ ≤ W.B0.eval (W.G0.eval (feature W m)) := h.B0_mono hi0
            _ ≤ W.G0.eval (W.B0.eval (feature W m)) := h.recode00 _ hnn
            _ = W.G0.eval (feature W (2 * m)) := by rw [feature_even W m hm]
        · calc
            feature W (3 * (2 * m) + 1) = W.B1.eval (feature W (3 * m)) := by
              rw [show 3 * (2 * m) + 1 = 2 * (3 * m) + 1 by omega]
              exact feature_odd W (3 * m) (by omega)
            _ ≤ W.B1.eval (W.G0.eval (feature W m)) := h.B1_mono hi0
            _ ≤ W.G1.eval (W.B0.eval (feature W m)) := h.recode10 _ hnn
            _ = W.G1.eval (feature W (2 * m)) := by rw [feature_even W m hm]
        · calc
            feature W (3 * (2 * m) + 2) = W.B0.eval (feature W (3 * m + 1)) := by
              rw [show 3 * (2 * m) + 2 = 2 * (3 * m + 1) by omega]
              exact feature_even W (3 * m + 1) (by omega)
            _ ≤ W.B0.eval (W.G1.eval (feature W m)) := h.B0_mono hi1
            _ ≤ W.G2.eval (W.B0.eval (feature W m)) := h.recode20 _ hnn
            _ = W.G2.eval (feature W (2 * m)) := by rw [feature_even W m hm]
      · obtain ⟨m, hmform⟩ : ∃ m : ℕ, n = 2 * m + 1 := ⟨n / 2, by omega⟩
        subst n
        have hm : 0 < m := by omega
        have hlt : m < 2 * m + 1 := by omega
        obtain ⟨hi0, hi1, hi2⟩ := ih m hlt hm
        have hnn := feature_nonneg W h m
        refine ⟨?_, ?_, ?_⟩
        · calc
            feature W (3 * (2 * m + 1)) = W.B1.eval (feature W (3 * m + 1)) := by
              rw [show 3 * (2 * m + 1) = 2 * (3 * m + 1) + 1 by omega]
              exact feature_odd W (3 * m + 1) (by omega)
            _ ≤ W.B1.eval (W.G1.eval (feature W m)) := h.B1_mono hi1
            _ ≤ W.G0.eval (W.B1.eval (feature W m)) := h.recode01 _ hnn
            _ = W.G0.eval (feature W (2 * m + 1)) := by rw [feature_odd W m hm]
        · calc
            feature W (3 * (2 * m + 1) + 1) = W.B0.eval (feature W (3 * m + 2)) := by
              rw [show 3 * (2 * m + 1) + 1 = 2 * (3 * m + 2) by omega]
              exact feature_even W (3 * m + 2) (by omega)
            _ ≤ W.B0.eval (W.G2.eval (feature W m)) := h.B0_mono hi2
            _ ≤ W.G1.eval (W.B1.eval (feature W m)) := h.recode11 _ hnn
            _ = W.G1.eval (feature W (2 * m + 1)) := by rw [feature_odd W m hm]
        · calc
            feature W (3 * (2 * m + 1) + 2) = W.B1.eval (feature W (3 * m + 2)) := by
              rw [show 3 * (2 * m + 1) + 2 = 2 * (3 * m + 2) + 1 by omega]
              exact feature_odd W (3 * m + 2) (by omega)
            _ ≤ W.B1.eval (W.G2.eval (feature W m)) := h.B1_mono hi2
            _ ≤ W.G2.eval (W.B1.eval (feature W m)) := h.recode21 _ hnn
            _ = W.G2.eval (feature W (2 * m + 1)) := by rw [feature_odd W m hm]

def certificateRank (W : Certificate d) (n : ℕ) : ℚ :=
  W.observe (feature W n)

theorem certificateRank_nonneg (W : Certificate d) (h : W.Semantics) (n : ℕ) :
    0 ≤ certificateRank W n := by
  exact h.observe_nonneg (feature_nonneg W h n)

theorem certificateRank_even (W : Certificate d) (h : W.Semantics)
    (m : ℕ) (hm : 0 < m) :
    certificateRank W m ≤ certificateRank W (2 * m) := by
  unfold certificateRank
  rw [feature_even W m hm]
  exact h.even_rank _ (feature_nonneg W h m)

theorem certificateRank_odd (W : Certificate d) (h : W.Semantics)
    (m : ℕ) (hm : 0 < m) :
    certificateRank W (3 * m + 2) + 1 ≤ certificateRank W (2 * m + 1) := by
  have ha := (arithmetic_adapter W h m hm).2.2
  have ho := h.observe_mono ha
  have hd := h.odd_rank _ (feature_nonneg W h m)
  unfold certificateRank
  rw [feature_odd W m hm]
  linarith

theorem valid_implies_shortcut_collatz (W : Certificate d) (hv : W.Valid) :
    ∀ n : ℕ, 0 < n → ReachesOne n := by
  have h := W.valid_semantics hv
  exact rational_rank_implies_collatz (certificateRank W)
    (fun n _ => certificateRank_nonneg W h n)
    (certificateRank_even W h) (certificateRank_odd W h)

theorem valid_implies_ordinary_collatz (W : Certificate d) (hv : W.Valid) :
    ∀ n : ℕ, 0 < n → OrdinaryReachesOne n := by
  intro n hn
  exact reachesOne_implies_ordinary (valid_implies_shortcut_collatz W hv n hn)

end PoincareSecond
