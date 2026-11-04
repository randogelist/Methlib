import HVRNativeLogRpow
import HVRNativeLSeriesNorm
import NativeMangoldtNonneg
import NativeMangoldtBound
import NativeSeriesInfrastructure
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
Candidate direct p-series majorization of the von Mangoldt L-series in
the half-plane `Re(s) > 1`. This version uses the separate pointwise bound
proved from the definition, in place of the divisor-sum argument. It does
not explicitly invoke the original von Mangoldt nonnegativity, prime-value,
power-value, divisor-sum, logarithmic-bound, or L-series summability theorems.
Compilation and recursive declaration-dependency inspection remain necessary.
-/

noncomputable section

namespace HVRNextSummability

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
  refine HVRNativeSeriesInfrastructure.complex_summable_of_majorant hmajorant ?_
  intro n
  rw [HVRNativeLSeriesNorm.norm_term]
  by_cases hn : n = 0
  · rw [if_pos hn]
    exact div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _) (le_of_lt hε)
  · rw [if_neg hn]
    have hnpos : (0 : ℝ) < (n : ℝ) := by
      exact_mod_cast (Nat.pos_of_ne_zero hn)
    have hlog : ArithmeticFunction.vonMangoldt n ≤ (n : ℝ) ^ ε / ε :=
      le_trans (HVRNativeMangoldtBound.vonMangoldt_le_log_native n)
        (HVRNativeLogRpow.log_natCast_le_rpow_div n hε)
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

end HVRNextSummability
