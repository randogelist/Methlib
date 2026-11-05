import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace CondFeffA

/-- The factorial bound required of a convergent time Taylor series with
unnormalized right derivatives `q n`. The integer absorbs both a series
bound and the reciprocal of a positive time radius. -/
def FactorialJetBound (q : ℕ → ℝ) : Prop :=
  ∃ m : ℕ, ∀ n : ℕ, |q n| ≤ (n.factorial : ℝ) * (m : ℝ) ^ (n + 1)


/-- A positive-radius analytic estimate with a real geometric constant
implies the corresponding integral-index bound. -/
theorem factorialJetBound_of_real_bound {q : ℕ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ n : ℕ, |q n| ≤ (n.factorial : ℝ) * M ^ (n + 1)) : FactorialJetBound q := by
  obtain ⟨m, hm⟩ := exists_nat_gt M
  refine ⟨m, ?_⟩
  intro n
  apply (h n).trans
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hM hm.le (n + 1))
    (by positivity)

/-- The witness n = m + 2 defeats the m-th candidate geometric bound. -/
theorem superfactorial_dominates_geometric (m : ℕ) :
    ∃ n : ℕ, 3 * (n.factorial * m ^ (n + 1)) < 2 * (2 * n + 3).factorial := by
  let n : ℕ := m + 2
  refine ⟨n, ?_⟩
  have hmn : m ≤ n := by dsimp [n]; omega
  have hn : 2 ≤ n := by dsimp [n]; omega
  have hpow : m ^ (n + 1) ≤ n ^ (n + 1) := by
    gcongr <;> omega
  have hthree : 3 ≤ n * n := by
    calc
      3 ≤ 2 * 2 := by decide
      _ ≤ n * n := Nat.mul_le_mul hn hn
  have hscaled : 3 * (n.factorial * m ^ (n + 1)) ≤ n.factorial * n ^ (n + 3) := by
    calc
      3 * (n.factorial * m ^ (n + 1)) ≤ (n * n) * (n.factorial * n ^ (n + 1)) :=
        Nat.mul_le_mul hthree (Nat.mul_le_mul_left n.factorial hpow)
      _ = n.factorial * n ^ (n + 3) := by
        rw [show n + 3 = (n + 1) + 2 by omega, pow_add n (n + 1) 2, pow_two]
        ring
  have hexponent : 2 * n + 3 - n = n + 3 := by omega
  have hblock : n.factorial * n ^ (n + 3) ≤ (2 * n + 3).factorial := by
    simpa only [hexponent] using
      (Nat.factorial_mul_pow_sub_le_factorial (n := n) (m := 2 * n + 3) (by omega))
  have hle := hscaled.trans hblock
  have hpos := Nat.factorial_pos (2 * n + 3)
  omega

/-- The superfactorial lower bound on the *linear amplitude coefficient*
of the NSE time jet rules out a factorial bound for that sequence. It does
not assign a numerical amplitude or assert that the full jet has this
lower bound at each amplitude. -/
theorem linear_jet_growth_excludes_factorial_bound {q : ℕ → ℝ}
    (hlower : ∀ n : ℕ, (2 / 3 : ℝ) * ((2 * n + 3).factorial : ℝ) ≤ |q n|) :
    ¬ FactorialJetBound q := by
  rintro ⟨m, hm⟩
  obtain ⟨n, hn⟩ := superfactorial_dominates_geometric m
  have hstrict :
      3 * ((n.factorial : ℝ) * (m : ℝ) ^ (n + 1)) <
        2 * ((2 * n + 3).factorial : ℝ) := by
    exact_mod_cast hn
  linarith [hlower n, hm n]

/-- Absolute value in the radial finite-sum formula at viscosity one. -/
noncomputable def radialLinearMagnitude (n : ℕ) : ℝ :=
  (2 / 3 : ℝ) * ((2 * n + 3).factorial : ℝ) *
    ∑ k ∈ Finset.range (n + 2), (1 : ℝ) / (k.factorial : ℝ)

/-- The k = 0 summand contributes exactly one; every remaining term is nonnegative. -/
theorem radial_linear_magnitude_lower (n : ℕ) :
    (2 / 3 : ℝ) * ((2 * n + 3).factorial : ℝ) ≤ radialLinearMagnitude n := by
  have partialSum (j : ℕ) :
      1 ≤ ∑ k ∈ Finset.range (j + 1), (1 : ℝ) / (k.factorial : ℝ) := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Finset.sum_range_succ]
      have hterm : 0 ≤ (1 : ℝ) / ((j + 1).factorial : ℝ) := by positivity
      exact le_trans ih (le_add_of_nonneg_right hterm)
  have hsum := partialSum (n + 1)
  have hfactor : 0 ≤ (2 / 3 : ℝ) * ((2 * n + 3).factorial : ℝ) := by positivity
  simpa only [radialLinearMagnitude, mul_one] using mul_le_mul_of_nonneg_left hsum hfactor

/-- Exact identification of the linear time-jet magnitudes with the
radial formula is sufficient for the growth step. -/
theorem exact_radial_coefficients_exclude_factorial_bound {q : ℕ → ℝ}
    (h : ∀ n : ℕ, |q n| = radialLinearMagnitude n) : ¬ FactorialJetBound q := by
  apply linear_jet_growth_excludes_factorial_bound
  intro n
  rw [h n]
  exact radial_linear_magnitude_lower n

end CondFeffA
