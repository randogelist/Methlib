import Mathlib.NumberTheory.Chebyshev
import Mathlib.Tactic

/-!
Candidate native derivation of the exact Chebyshev upper bound.

No local Lean execution or theorem-level axiom audit has been performed for
this file.  In particular, this is not yet an A-tier result.

The proof DOES NOT invoke `Chebyshev.theta_le_log4_mul_x` or a PNT endpoint.
It does use Mathlib's elementary primorial/central-binomial building blocks
`primorial_add_le`, `primorial_succ`, `Nat.choose_middle_le_pow`, and
`Chebyshev.theta_eq_log_primorial`.  The source-level dependencies of those
building blocks must still be checked recursively before claiming independence
from the target or other prohibited results.  This is not an all-native
construction from elementary prime factorization and is not a Mathlib-free
proof.

The primorial induction follows the elementary central-binomial argument also
used by Mathlib's `Mathlib/NumberTheory/Primorial.lean`; see that file and its
Apache-2.0 copyright notice for attribution.  Mathlib revision intended for
the eventual external run: fd9375dc1e3b113b2ddc599f4ebb59d11d4c60d0.
-/

noncomputable section

namespace HVRNativeChebyshevBound

/-- A candidate central-binomial proof for the elementary primorial bound. -/
theorem primorial_lt_four_pow_native (n : ℕ) (hn : n ≠ 0) :
    primorial n < 4 ^ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => exact False.elim (hn rfl)
    | succ k =>
      rcases k.even_or_odd with ⟨m, rfl⟩ | hkodd
      · by_cases hm0 : m = 0
        · subst m
          decide
        · have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
          have hprior : primorial (m + 1) < 4 ^ (m + 1) :=
            ih (m + 1) (by omega) (by omega)
          have hsplit : primorial ((m + 1) + m) ≤
              primorial (m + 1) * Nat.choose ((m + 1) + m) (m + 1) :=
            primorial_add_le (by omega)
          have hindex : (m + 1) + m = 2 * m + 1 := by omega
          rw [hindex, Nat.choose_symm_half] at hsplit
          have hmiddle : Nat.choose (2 * m + 1) m ≤ 4 ^ m :=
            Nat.choose_middle_le_pow m
          have hproduct : primorial (2 * m + 1) <
              4 ^ (m + 1) * 4 ^ m :=
            lt_of_le_of_lt hsplit
              (Nat.mul_lt_mul_of_lt_of_le hprior hmiddle (by simp))
          have hpow : 4 ^ (m + 1) * 4 ^ m = 4 ^ (2 * m + 1) := by
            rw [← pow_add]
            congr 1 <;> omega
          rw [hpow] at hproduct
          simpa only [two_mul, Nat.succ_eq_add_one] using hproduct
      · by_cases hk1 : k = 1
        · subst k
          decide
        · have hk0 : k ≠ 0 := by
            intro h
            subst k
            simp at hkodd
          have hprior : primorial k < 4 ^ k :=
            ih k (Nat.lt_succ_self k) hk0
          have heq : primorial (k + 1) = primorial k :=
            primorial_succ hk1 hkodd
          have hpow : 4 ^ k ≤ 4 ^ (k + 1) :=
            Nat.pow_le_pow_right (by decide) (Nat.le_succ k)
          simpa only [Nat.succ_eq_add_one, heq] using lt_of_lt_of_le hprior hpow

theorem primorial_le_four_pow_native (n : ℕ) : primorial n ≤ 4 ^ n := by
  by_cases hn : n = 0
  · subst n
    decide
  · exact (primorial_lt_four_pow_native n hn).le

/-- Exact theta upper bound, via the candidate central-binomial induction. -/
theorem theta_le_log4_mul_x_native {x : ℝ} (hx : 0 ≤ x) :
    Chebyshev.theta x ≤ Real.log 4 * x := by
  rw [Chebyshev.theta_eq_log_primorial]
  calc
    Real.log (primorial ⌊x⌋₊ : ℝ) ≤ Real.log ((4 : ℝ) ^ ⌊x⌋₊) := by
      apply Real.log_le_log
      · exact_mod_cast primorial_pos ⌊x⌋₊
      · exact_mod_cast primorial_le_four_pow_native ⌊x⌋₊
    _ = Real.log 4 * (⌊x⌋₊ : ℝ) := by rw [Real.log_pow]; ring
    _ ≤ Real.log 4 * x := by
      exact mul_le_mul_of_nonneg_left (Nat.floor_le hx) (Real.log_nonneg (by norm_num))

end HVRNativeChebyshevBound
