import BinaryAdapter

namespace PoincareSecond

def operationName : String :=
  "Operation POINCARE PARAMETER RESEARCH FRONTIER THE SECOND"

theorem CHECKER_SOUND_SHORTCUT {d : ℕ} (W : Certificate d)
    (h : W.check = true) : ∀ n : ℕ, 0 < n → ReachesOne n := by
  exact valid_implies_shortcut_collatz W ((W.check_eq_true_iff).mp h)

theorem CHECKER_SOUND {d : ℕ} (W : Certificate d)
    (h : W.check = true) : ∀ n : ℕ, 0 < n → OrdinaryReachesOne n := by
  exact valid_implies_ordinary_collatz W ((W.check_eq_true_iff).mp h)

theorem FINITE_WITNESS_IMPLIES_COLLATZ
    (h : ∃ d : ℕ, ∃ W : Certificate d, W.check = true) :
    ∀ n : ℕ, 0 < n → OrdinaryReachesOne n := by
  obtain ⟨d, W, hW⟩ := h
  exact CHECKER_SOUND W hW

#check Certificate.check
#check Certificate.check_eq_true_iff
#check arithmetic_adapter
#check CHECKER_SOUND_SHORTCUT
#check CHECKER_SOUND
#check FINITE_WITNESS_IMPLIES_COLLATZ

#print axioms Certificate.valid_semantics
#print axioms arithmetic_adapter
#print axioms rational_rank_implies_collatz
#print axioms CHECKER_SOUND_SHORTCUT
#print axioms CHECKER_SOUND
#print axioms FINITE_WITNESS_IMPLIES_COLLATZ

end PoincareSecond
