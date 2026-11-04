import HVR_HigherCoefficient_Geometric

/-!
The single-prime geometric factor for the actual von Mangoldt coefficients,
inspired by snditeration's real Bose geometric expansion.  The argument is
valid for every complex s with 0 < s.re.  It says nothing about convergence
after summing over primes or identifying that sum with the zeta logarithmic
derivative.  It still uses Mathlib's geometric-series theorem.
-/

noncomputable section

open scoped BigOperators

namespace HVRSnditerationPrimePowerTail

open HVRZetaLogDerivative HVRPrimeZetaSplit HVRPrimePowerCorrection
open HVRPowerCorrectionHolomorphic HVRCorrectionTermHolomorphic
open HVRHigherCoefficientGeometric

theorem prime_ratio_norm_lt_one {p : ℕ} (hp : Nat.Prime p) (s : ℂ)
    (hs : 0 < s.re) : ‖complexRatio p s‖ < 1 := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hlog : 0 < Real.log (p : ℝ) := Real.log_pos hp1
  have harg : -s.re * Real.log (p : ℝ) < 0 := by
    have hm := mul_pos hs hlog
    linarith
  rw [complexRatio_norm]
  change Real.exp (-s.re * Real.log (p : ℝ)) < 1
  exact Real.exp_lt_one_iff.mpr harg

theorem higher_prime_power_hasSum {p : ℕ} (hp : Nat.Prime p) (s : ℂ)
    (hs : 0 < s.re) :
    HasSum (fun k : ℕ => LSeries.term higherCoefficientC s (p ^ (k + 2)))
      (complexCorrectionTerm p s) := by
  have hgeom := hasSum_geometric_of_norm_lt_one (prime_ratio_norm_lt_one hp s hs)
  have hscaled := hgeom.mul_left
    ((Real.log (p : ℝ) : ℂ) * (complexRatio p s) ^ 2)
  have hfun :
      (fun k : ℕ => LSeries.term higherCoefficientC s (p ^ (k + 2))) =
      (fun k : ℕ => ((Real.log (p : ℝ) : ℂ) * (complexRatio p s) ^ 2) *
        (complexRatio p s) ^ k) := by
    funext k
    rw [higher_lseries_term_prime_power hp, pow_add]
    ring
  rw [hfun]
  simpa only [complexCorrectionTerm, if_pos hp, div_eq_mul_inv] using hscaled

theorem mangoldt_term_prime_power {p : ℕ} (hp : Nat.Prime p) (s : ℂ) (k : ℕ) :
    LSeries.term vonMangoldtC s (p ^ (k + 1)) =
      (Real.log (p : ℝ) : ℂ) * (complexRatio p s) ^ (k + 1) := by
  have hzero : vonMangoldtC 0 = 0 := by simp [vonMangoldtC]
  rw [LSeries.term_def₀ hzero]
  have hv : ArithmeticFunction.vonMangoldt (p ^ (k + 1)) = Real.log (p : ℝ) :=
    vonMangoldt_at_prime_pow hp (by omega)
  rw [show vonMangoldtC (p ^ (k + 1)) = (Real.log (p : ℝ) : ℂ) by
    simp only [vonMangoldtC, hv]]
  rw [cpow_prime_power_eq_ratio hp]

theorem mangoldt_prime_power_hasSum {p : ℕ} (hp : Nat.Prime p) (s : ℂ)
    (hs : 0 < s.re) :
    HasSum (fun k : ℕ => LSeries.term vonMangoldtC s (p ^ (k + 1)))
      ((Real.log (p : ℝ) : ℂ) * complexRatio p s / (1 - complexRatio p s)) := by
  have hgeom := hasSum_geometric_of_norm_lt_one (prime_ratio_norm_lt_one hp s hs)
  have hscaled := hgeom.mul_left ((Real.log (p : ℝ) : ℂ) * complexRatio p s)
  have hfun :
      (fun k : ℕ => LSeries.term vonMangoldtC s (p ^ (k + 1))) =
      (fun k : ℕ => ((Real.log (p : ℝ) : ℂ) * complexRatio p s) *
        (complexRatio p s) ^ k) := by
    funext k
    rw [mangoldt_term_prime_power hp, pow_succ]
    ring
  rw [hfun]
  simpa only [div_eq_mul_inv] using hscaled

theorem mangoldt_prime_power_tsum {p : ℕ} (hp : Nat.Prime p) (s : ℂ)
    (hs : 0 < s.re) :
    (∑' k : ℕ, LSeries.term vonMangoldtC s (p ^ (k + 1))) =
      (Real.log (p : ℝ) : ℂ) * complexRatio p s / (1 - complexRatio p s) :=
  (mangoldt_prime_power_hasSum hp s hs).tsum_eq

end HVRSnditerationPrimePowerTail
