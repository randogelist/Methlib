import NativeMangoldtNonneg
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
Direct p-series majorization of the von Mangoldt L-series on Re(s) > 1.

This candidate does not call the existing von Mangoldt L-series summability
theorem or project wrappers derived from it. Its explicit nonnegativity
step and the divisor-sum bound use NativeMangoldtNonneg. The divisor-sum
identity remains a Mathlib dependency and requires transitive dependency
inspection for independence claims. It retains elementary Mathlib
ingredients, including the pointwise bound on von Mangoldt, the norm of an
L-series term, the logarithm-vs-power inequality, and real p-series
summability. Its source has not yet been compiled or audited.
-/

noncomputable section

namespace HVRNativeSummabilityUnified

/-- The von Mangoldt coefficient is bounded by the logarithm, obtained
from the divisor-sum identity and the project nonnegativity theorem. -/
theorem vonMangoldt_le_log_native : ∀ n : ℕ,
    ArithmeticFunction.vonMangoldt n ≤ Real.log (n : ℝ)
  | 0 => by simp
  | n + 1 => by
    rw [← ArithmeticFunction.vonMangoldt_sum]
    exact Finset.single_le_sum
      (fun i _ => HVRNativeMangoldtNonneg.vonMangoldt_nonneg_native i)
      (Nat.mem_divisors_self _ n.succ_ne_zero)

/-- The actual von Mangoldt L-series converges for all complex `s` with
real part greater than one, by a p-series majorant. -/
theorem vonMangoldt_lseries_summable {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) s := by
  let ε : ℝ := (s.re - 1) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hexponent : ε - s.re < -1 := by dsimp [ε]; linarith
  have hpseries : Summable (fun n : ℕ => (n : ℝ) ^ (ε - s.re)) :=
    Real.summable_nat_rpow.mpr hexponent
  have hmajorant : Summable (fun n : ℕ => (n : ℝ) ^ (ε - s.re) / ε) :=
    hpseries.div_const ε
  change Summable (LSeries.term
    (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) s)
  apply Summable.of_norm
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) ?_ hmajorant
  intro n
  rw [LSeries.norm_term_eq]
  by_cases hn : n = 0
  · rw [if_pos hn]
    exact div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _) (le_of_lt hε)
  · rw [if_neg hn]
    have hnpos : (0 : ℝ) < (n : ℝ) := by
      exact_mod_cast (Nat.pos_of_ne_zero hn)
    have hlog : ArithmeticFunction.vonMangoldt n ≤ (n : ℝ) ^ ε / ε :=
      le_trans (vonMangoldt_le_log_native n)
        (Real.log_natCast_le_rpow_div n hε)
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (HVRNativeMangoldtNonneg.vonMangoldt_nonneg_native n)]
    calc
      ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ s.re =
          ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-s.re) := by
        rw [div_eq_mul_inv, Real.rpow_neg (Nat.cast_nonneg n)]
      _ ≤
          ((n : ℝ) ^ ε / ε) * (n : ℝ) ^ (-s.re) :=
        mul_le_mul_of_nonneg_right hlog (Real.rpow_nonneg (Nat.cast_nonneg n) _)
      _ = (n : ℝ) ^ (ε - s.re) / ε := by
        rw [show ε - s.re = ε + (-s.re) by ring, Real.rpow_add hnpos]
        ring

end HVRNativeSummabilityUnified
