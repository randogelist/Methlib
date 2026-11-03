import NextSummability
import NativeSeriesInfrastructure
import HVRNativePrimePowerRegroup
import HVRPrimePowComplexNoOldLog
import HVRComplexNormExpNative
import NativeMangoldtPrime
import NativeMangoldtPow
import NativeZetaLogDerivative
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Tactic

/-!
Candidate integrated prime-power reindexing proof. Uses the scoped regrouping,
series infrastructure, direct bounded summability, and positive-prime complex
power reconstruction. The exact conclusion is the existing HVR
`PrimePowerReindexing` proposition. Source candidate only: no Lean compiler or
theorem audit has verified this integrated proof. The imported replacements
still rely on general Mathlib results; inspect transitive dependencies.
-/

noncomputable section
open scoped BigOperators

namespace HVRNextPrimePowerReindex

/-- The complex ratio at a prime, written as an exponential. -/
def primeRatio (p : ℕ) (s : ℂ) : ℂ :=
  Complex.exp (-s * (Real.log (p : ℝ) : ℂ))

theorem primeRatio_eq_cpow {p : ℕ} (hp : Nat.Prime p) (s : ℂ) :
    primeRatio p s = (p : ℂ) ^ (-s) := by
  simpa only [pow_one, primeRatio] using
    (HVRPrimePowComplexNoOldLog.prime_pow_cpow_eq_ratio hp 1 s).symm

theorem primeRatio_norm_lt_one {p : ℕ} (hp : Nat.Prime p) {s : ℂ}
    (hs : 1 < s.re) : ‖primeRatio p s‖ < 1 := by
  have hlog : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hneg : -s.re * Real.log (p : ℝ) < 0 := by nlinarith
  have hexp : Real.exp (-s.re * Real.log (p : ℝ)) < 1 :=
    Real.exp_lt_one_iff.mpr hneg
  simpa only [primeRatio, HVRComplexNormExpNative.norm_exp_rebuild, Complex.mul_re,
    Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    using hexp

theorem cpow_prime_power_eq_primeRatio {p : ℕ} (hp : Nat.Prime p)
    (m : ℕ) (s : ℂ) :
    ((p ^ m : ℕ) : ℂ) ^ (-s) = (primeRatio p s) ^ m := by
  simpa only [primeRatio] using HVRPrimePowComplexNoOldLog.prime_pow_cpow_eq_ratio hp m s

def mangoldtC (n : ℕ) : ℂ := (ArithmeticFunction.vonMangoldt n : ℂ)

theorem mangoldtC_zero : mangoldtC 0 = 0 := by simp [mangoldtC]

theorem mangoldt_term_prime_power (s : ℂ) (p : Nat.Primes) (k : ℕ) :
    LSeries.term mangoldtC s ((p : ℕ) ^ (k + 1)) =
      (Real.log ((p : ℕ) : ℝ) : ℂ) * (primeRatio p s) ^ (k + 1) := by
  rw [LSeries.term_def₀ mangoldtC_zero]
  have hv : ArithmeticFunction.vonMangoldt ((p : ℕ) ^ (k + 1)) =
      Real.log ((p : ℕ) : ℝ) := by
    rw [HVRNativeMangoldtPow.vonMangoldt_apply_pow_native (by omega),
      HVRNativeMangoldtPrime.vonMangoldt_apply_prime_native p.property]
  rw [show mangoldtC ((p : ℕ) ^ (k + 1)) =
      (Real.log ((p : ℕ) : ℝ) : ℂ) by simp only [mangoldtC, hv]]
  rw [cpow_prime_power_eq_primeRatio p.property]

theorem mangoldt_lseries_support (s : ℂ) :
    Function.support (LSeries.term mangoldtC s) ⊆ {n : ℕ | IsPrimePow n} := by
  intro n hn
  change LSeries.term mangoldtC s n ≠ 0 at hn
  by_contra hnp
  change ¬ IsPrimePow n at hnp
  have hzero : ArithmeticFunction.vonMangoldt n = 0 := by
    change (if IsPrimePow n then Real.log (Nat.minFac n) else 0) = 0
    simp only [if_neg hnp]
  apply hn
  simp [LSeries.term_def, mangoldtC, hzero]

/-- For one prime, sum its actual prime-power terms as a geometric series. -/
theorem prime_power_tsum (s : ℂ) (hs : 1 < s.re) (p : Nat.Primes) :
    (∑' k : ℕ, LSeries.term mangoldtC s ((p : ℕ) ^ (k + 1))) =
      HVRNativeZetaLogDerivative.primeEulerTerm s p := by
  have hq := primeRatio_norm_lt_one p.property hs
  have hg := HVRNativeSeriesInfrastructure.hasSum_scale (hasSum_geometric_of_norm_lt_one hq)
    ((Real.log ((p : ℕ) : ℝ) : ℂ) * primeRatio p s)
  have hfun :
      (fun k : ℕ => LSeries.term mangoldtC s ((p : ℕ) ^ (k + 1))) =
      (fun k : ℕ => ((Real.log ((p : ℕ) : ℝ) : ℂ) * primeRatio p s) *
        (primeRatio p s) ^ k) := by
    funext k
    rw [mangoldt_term_prime_power, pow_succ]
    ring
  rw [hfun]
  have hsum := HVRNativeSeriesInfrastructure.hasSum_identifies_tsum hg
  unfold HVRNativeZetaLogDerivative.primeEulerTerm
  rw [← primeRatio_eq_cpow p.property]
  simpa only [div_eq_mul_inv, mul_assoc] using hsum

/-- Actual prime-power reindexing on the full strict half-plane. -/
theorem primePowerReindexing : HVRNativeZetaLogDerivative.PrimePowerReindexing := by
  intro s hs
  have hsum : Summable (LSeries.term mangoldtC s) := by
    exact HVRNextSummability.vonMangoldt_lseries_summable hs
  have hindex := HVRNativePrimePowerRegroup.regroup
    hsum (mangoldt_lseries_support s)
  change (∑' n : ℕ, LSeries.term mangoldtC s n) =
    HVRNativeZetaLogDerivative.primeEulerSeries s
  rw [hindex]
  unfold HVRNativeZetaLogDerivative.primeEulerSeries
  apply tsum_congr
  intro p
  exact prime_power_tsum s hs p

end HVRNextPrimePowerReindex
