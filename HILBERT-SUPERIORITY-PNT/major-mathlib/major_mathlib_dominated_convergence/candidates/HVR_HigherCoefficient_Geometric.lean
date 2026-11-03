import HVR_HigherCoefficient_Reindex
import HVR_Correction_UniformBound
import Mathlib.Analysis.SpecificLimits.Normed

noncomputable section

/-!
Candidate geometric evaluation of the higher prime-power summands.
No local Lean run has been performed. This module does not prove PNT.
-/
namespace HVRHigherCoefficientGeometric

open HVRZetaLogDerivative HVRPrimeZetaSplit HVRPrimePowerCorrection
open HVRPowerCorrectionHolomorphic HVRCorrectionTermHolomorphic

/-- Coefficients at prime powers with exponent at least two. -/
theorem higherCoefficient_prime_power {p k : ℕ} (hp : Nat.Prime p) :
    higherCoefficient (p ^ (k + 2)) = Real.log (p : ℝ) := by
  have hk : k + 2 ≠ 0 := by omega
  have hnp : ¬ Nat.Prime (p ^ (k + 2)) := Nat.Prime.not_prime_pow (by omega)
  simp only [higherCoefficient, primeCoefficient, hnp, if_false, sub_zero,
    vonMangoldt_at_prime_pow hp hk]

/-- The exponential ratio agrees with the usual complex power. -/
theorem complexRatio_eq_cpow_neg {p : ℕ} (hp : Nat.Prime p) (s : ℂ) :
    complexRatio p s = (p : ℂ) ^ (-s) := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [Complex.cpow_def_of_ne_zero hp0]
  have hlog : Complex.log (p : ℂ) = (Real.log (p : ℝ) : ℂ) := by
    simpa using (Complex.ofReal_log (show (0 : ℝ) ≤ (p : ℝ) by positivity)).symm
  rw [hlog]
  unfold complexRatio
  congr 1
  ring

/-- Complex powers of natural prime powers are powers of the prime ratio. -/
theorem cpow_prime_power_eq_ratio {p : ℕ} (hp : Nat.Prime p) (m : ℕ) (s : ℂ) :
    ((p ^ m : ℕ) : ℂ) ^ (-s) = (complexRatio p s) ^ m := by
  calc
    ((p ^ m : ℕ) : ℂ) ^ (-s) = ((p : ℂ) ^ m) ^ (-s) := by rw [Nat.cast_pow]
    _ = (p : ℂ) ^ ((m : ℂ) * (-s)) :=
      (Complex.natCast_cpow_natCast_mul p m (-s)).symm
    _ = ((p : ℂ) ^ (-s)) ^ m := Complex.cpow_nat_mul (p : ℂ) m (-s)
    _ = (complexRatio p s) ^ m := by rw [complexRatio_eq_cpow_neg hp]

/-- Each actual L-series term is the corresponding geometric summand. -/
theorem higher_lseries_term_prime_power {p : ℕ} (hp : Nat.Prime p)
    (k : ℕ) (s : ℂ) :
    LSeries.term higherCoefficientC s (p ^ (k + 2)) =
      (Real.log (p : ℝ) : ℂ) * (complexRatio p s) ^ (k + 2) := by
  have hzero : higherCoefficientC 0 = 0 := by
    simp [higherCoefficientC, higherCoefficient, primeCoefficient]
  rw [LSeries.term_def₀ hzero]
  rw [show higherCoefficientC (p ^ (k + 2)) = (Real.log (p : ℝ) : ℂ) by
    simp only [higherCoefficientC, higherCoefficient_prime_power hp]]
  rw [cpow_prime_power_eq_ratio hp]

/-- Each prime-power tail is the geometric correction at that prime. -/
theorem correction_prime_power_hasSum {p : ℕ} (hp : Nat.Prime p)
    (sigma t : ℝ) (hsigma : 1 < sigma) :
    HasSum (fun k : ℕ => LSeries.term higherCoefficientC (zetaPoint sigma t)
      (p ^ (k + 2))) (complexCorrectionTerm p (zetaPoint sigma t)) := by
  have hsigma' : (1 / 2 : ℝ) < sigma := by linarith
  have hre : (zetaPoint sigma t).re = sigma := by simp [zetaPoint]
  have hsmall : ‖complexRatio p (zetaPoint sigma t)‖ < 1 := by
    rw [complexRatio_norm, hre]
    have hle := ratio_le_two sigma hsigma' hp
    have hpos := denominator_uniform_pos sigma hsigma'
    linarith
  have hgeom := hasSum_geometric_of_norm_lt_one hsmall
  have hscaled := hgeom.mul_left
    ((Real.log (p : ℝ) : ℂ) * (complexRatio p (zetaPoint sigma t)) ^ 2)
  have hfun :
      (fun k : ℕ => LSeries.term higherCoefficientC (zetaPoint sigma t)
        (p ^ (k + 2))) =
      (fun k : ℕ => ((Real.log (p : ℝ) : ℂ) *
        (complexRatio p (zetaPoint sigma t)) ^ 2) *
        (complexRatio p (zetaPoint sigma t)) ^ k) := by
    funext k
    rw [higher_lseries_term_prime_power hp, pow_add]
    ring
  rw [hfun]
  simpa only [complexCorrectionTerm, if_pos hp, div_eq_mul_inv] using hscaled

theorem correction_prime_power_tsum {p : ℕ} (hp : Nat.Prime p)
    (sigma t : ℝ) (hsigma : 1 < sigma) :
    (∑' k : ℕ, LSeries.term higherCoefficientC (zetaPoint sigma t)
      (p ^ (k + 2))) = complexCorrectionTerm p (zetaPoint sigma t) :=
  (correction_prime_power_hasSum hp sigma t hsigma).tsum_eq

end HVRHigherCoefficientGeometric
