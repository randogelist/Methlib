import HVRComplexLogNative
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Tactic

/-!
Scoped replacement candidate for the complex-power rearrangement needed in
prime-power reindexing. The argument follows the nonzero branch of complex
power, the real logarithm of a natural power, and the exponential addition law.
It does not directly invoke `Complex.natCast_cpow_natCast_mul`,
`Complex.cpow_nat_mul`, or `Complex.cpow_def_of_ne_zero`.

Source candidate only. It must be compiled and audited externally. Dependencies
still include complex exponential and real/complex logarithm infrastructure;
independence from named declarations requires separate proof-dependency tracing.
-/

noncomputable section

namespace HVRPrimePowComplexNoOldLog

/-- Complex powers of positive natural powers, expanded via real logarithms. -/
theorem nat_pow_cpow_eq_exp_pow {p : ℕ} (hp : p ≠ 0) (m : ℕ) (z : ℂ) :
    ((p ^ m : ℕ) : ℂ) ^ z =
      Complex.exp ((Real.log (p : ℝ) : ℂ) * z) ^ m := by
  have hp0 : ((p ^ m : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (pow_ne_zero m hp)
  have hlog : Complex.log ((p ^ m : ℕ) : ℂ) =
      (((m : ℝ) * Real.log (p : ℝ) : ℝ) : ℂ) := by
    calc
      Complex.log ((p ^ m : ℕ) : ℂ) =
          (Real.log ((p ^ m : ℕ) : ℝ) : ℂ) := by
        exact HVRComplexLogNative.complex_log_nat (p ^ m)
      _ = (((m : ℝ) * Real.log (p : ℝ) : ℝ) : ℂ) := by
        rw [Nat.cast_pow, Real.log_pow]
  calc
    ((p ^ m : ℕ) : ℂ) ^ z =
        Complex.exp ((m : ℂ) * ((Real.log (p : ℝ) : ℂ) * z)) := by
      rw [Complex.cpow_def, if_neg hp0, hlog]
      rw [Complex.ofReal_mul, Complex.ofReal_natCast]
      congr 1
      ring
    _ = Complex.exp ((Real.log (p : ℝ) : ℂ) * z) ^ m :=
      Complex.exp_nat_mul _ m

/-- The exact prime-ratio power identity needed by the reindexing chain. -/
theorem prime_pow_cpow_eq_ratio {p : ℕ} (hp : Nat.Prime p) (m : ℕ) (s : ℂ) :
    ((p ^ m : ℕ) : ℂ) ^ (-s) =
      Complex.exp (-s * (Real.log (p : ℝ) : ℂ)) ^ m := by
  rw [nat_pow_cpow_eq_exp_pow hp.ne_zero]
  congr 1
  ring

end HVRPrimePowComplexNoOldLog
