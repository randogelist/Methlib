import Mathlib

/-!
# A rational rank implies Collatz termination

`iterateMap f k n` applies `f` exactly `k` times to `n`.  The recursion
places the first step outside the recursive call's starting argument:
`iterateMap f (k + 1) n = iterateMap f k (f n)`.

The proof below does not require the rank to decrease on even steps.
It uses induction on a natural strict upper bound for the rank, and
strong induction on the integer for the even steps within that bound.

This file has not been checked with a Lean compiler in this workspace.
-/

namespace PoincareSecond

/-- The shortcut Collatz map on natural numbers. -/
def shortcut (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else (3 * n + 1) / 2

/-- Finite iteration, with a recursion convenient for prefixing one step. -/
def iterateMap (f : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, n => n
  | k + 1, n => iterateMap f k (f n)

/-- The shortcut orbit of `n` reaches `1` after finitely many steps. -/
def ReachesOne (n : ℕ) : Prop :=
  ∃ k : ℕ, iterateMap shortcut k n = 1

theorem reachesOne_one : ReachesOne 1 := by
  exact ⟨0, rfl⟩

/-- A terminating successor gives a terminating starting point. -/
theorem reachesOne_of_shortcut {n : ℕ}
    (h : ReachesOne (shortcut n)) : ReachesOne n := by
  rcases h with ⟨k, hk⟩
  refine ⟨k + 1, ?_⟩
  change iterateMap shortcut k (shortcut n) = 1
  exact hk

/--
A nonnegative rational rank which is nonincreasing on even steps and
decreases by at least one on odd steps proves the shortcut Collatz
conjecture for every positive natural number.

The odd hypothesis starts at `m > 0`: it applies to odd inputs greater
than one, and makes no impossible decrease requirement at the target `1`.
-/
theorem rational_rank_implies_collatz
    (R : ℕ → ℚ)
    (hpos : ∀ n : ℕ, 0 < n → 0 ≤ R n)
    (heven : ∀ m : ℕ, 0 < m → R m ≤ R (2 * m))
    (hodd : ∀ m : ℕ, 0 < m → R (3 * m + 2) + 1 ≤ R (2 * m + 1)) :
    ∀ n : ℕ, 0 < n → ReachesOne n := by
  have hbounded : ∀ b : ℕ, ∀ n : ℕ,
      0 < n → R n < (b : ℚ) → ReachesOne n := by
    intro b
    induction b with
    | zero =>
        intro n hn hr
        have hp : (0 : ℚ) ≤ R n := hpos n hn
        have hr' : R n < (0 : ℚ) := by simpa using hr
        exact False.elim ((not_lt_of_ge hp) hr')
    | succ b ih =>
        intro n
        induction n using Nat.strong_induction_on with
        | h n ihn =>
            intro hn hr
            by_cases h1 : n = 1
            · rw [h1]
              exact reachesOne_one
            · by_cases hpar : n % 2 = 0
              · let m : ℕ := n / 2
                have heq : n = 2 * m := by
                  dsimp [m]
                  omega
                have hm : 0 < m := by omega
                have hmn : m < n := by omega
                have hrm : R m < ((Nat.succ b : ℕ) : ℚ) := by
                  calc
                    R m ≤ R (2 * m) := heven m hm
                    _ = R n := by rw [heq]
                    _ < ((Nat.succ b : ℕ) : ℚ) := hr
                have hs : shortcut n = m := by
                  simp [shortcut, hpar, m]
                apply reachesOne_of_shortcut
                rw [hs]
                exact ihn m hmn hm hrm
              · let m : ℕ := n / 2
                have heq : n = 2 * m + 1 := by
                  dsimp [m]
                  omega
                have hm : 0 < m := by omega
                have hr' : R (2 * m + 1) < (b : ℚ) + 1 := by
                  simpa only [heq, Nat.cast_succ] using hr
                have hdrop : R (3 * m + 2) + 1 ≤ R (2 * m + 1) :=
                  hodd m hm
                have hrnext : R (3 * m + 2) < (b : ℚ) := by
                  linarith
                have hnext : 0 < 3 * m + 2 := by omega
                have hs : shortcut n = 3 * m + 2 := by
                  unfold shortcut
                  rw [if_neg hpar]
                  omega
                apply reachesOne_of_shortcut
                rw [hs]
                exact ih (3 * m + 2) hnext hrnext
  intro n hn
  obtain ⟨b, hb⟩ := exists_nat_gt (R n)
  exact hbounded b n hn hb

/-- The ordinary, unaccelerated Collatz map. -/
def ordinaryCollatz (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else 3 * n + 1

/-- The ordinary Collatz orbit reaches `1` after finitely many steps. -/
def OrdinaryReachesOne (n : ℕ) : Prop :=
  ∃ k : ℕ, iterateMap ordinaryCollatz k n = 1

/-- Split a finite iteration into a prefix and a suffix. -/
theorem iterateMap_add (f : ℕ → ℕ) (a b n : ℕ) :
    iterateMap f (a + b) n = iterateMap f b (iterateMap f a n) := by
  induction a generalizing n with
  | zero =>
      simp [iterateMap]
  | succ a ih =>
      simpa only [Nat.succ_add, iterateMap] using ih (f n)

/-- One shortcut step is one or two ordinary Collatz steps. -/
theorem shortcut_step_ordinary (n : ℕ) :
    ∃ k : ℕ, iterateMap ordinaryCollatz k n = shortcut n := by
  by_cases hpar : n % 2 = 0
  · refine ⟨1, ?_⟩
    simp [iterateMap, ordinaryCollatz, shortcut, hpar]
  · have hnext : (3 * n + 1) % 2 = 0 := by omega
    refine ⟨2, ?_⟩
    simp [iterateMap, ordinaryCollatz, shortcut, hpar, hnext]

/-- Every finite shortcut orbit segment has an ordinary simulation. -/
theorem shortcut_iterate_simulated (k n : ℕ) :
    ∃ l : ℕ, iterateMap ordinaryCollatz l n = iterateMap shortcut k n := by
  induction k generalizing n with
  | zero =>
      exact ⟨0, rfl⟩
  | succ k ih =>
      rcases shortcut_step_ordinary n with ⟨a, ha⟩
      rcases ih (shortcut n) with ⟨b, hb⟩
      refine ⟨a + b, ?_⟩
      rw [iterateMap_add, ha]
      exact hb

/-- Shortcut termination implies ordinary Collatz termination. -/
theorem reachesOne_implies_ordinary {n : ℕ}
    (h : ReachesOne n) : OrdinaryReachesOne n := by
  rcases h with ⟨k, hk⟩
  rcases shortcut_iterate_simulated k n with ⟨l, hl⟩
  exact ⟨l, hl.trans hk⟩

/-- The same rational-rank hypotheses also prove ordinary termination. -/
theorem rational_rank_implies_ordinary_collatz
    (R : ℕ → ℚ)
    (hpos : ∀ n : ℕ, 0 < n → 0 ≤ R n)
    (heven : ∀ m : ℕ, 0 < m → R m ≤ R (2 * m))
    (hodd : ∀ m : ℕ, 0 < m → R (3 * m + 2) + 1 ≤ R (2 * m + 1)) :
    ∀ n : ℕ, 0 < n → OrdinaryReachesOne n := by
  intro n hn
  exact reachesOne_implies_ordinary
    (rational_rank_implies_collatz R hpos heven hodd n hn)

end PoincareSecond
