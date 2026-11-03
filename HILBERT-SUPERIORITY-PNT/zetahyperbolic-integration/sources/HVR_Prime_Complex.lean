import HVR_Prime_InfiniteGram
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

open scoped BigOperators

noncomputable section

/-!
A genuine complex prime series, with a cosine-moment bridge.
The prime term uses the convergent real prime weights and a unit phase.
It is proved equal term-by-term to the complex Dirichlet expression.
No zeta logarithmic derivative or zero-free claim is made.
-/
namespace HVRPrimeComplex

open HVRPrimeSummability HVRPrimeInfinite

def primeTerm (sigma t frequency : ℝ) (n : ℕ) : ℂ :=
  (primeWeightSeries sigma n : ℂ) *
    Complex.exp (((-(frequency * (t * Real.log (n : ℝ))) : ℝ) : ℂ) * Complex.I)

def primeSeries (sigma t frequency : ℝ) : ℂ :=
  ∑' n : ℕ, primeTerm sigma t frequency n

theorem primeTerm_summable (sigma t frequency : ℝ) (hsigma : 1 < sigma) :
    Summable (primeTerm sigma t frequency) := by
  apply Summable.of_norm_bounded (primeWeightSeries_summable sigma hsigma)
  intro n
  simp only [primeTerm, norm_mul, Complex.norm_real,
    Complex.norm_exp_ofReal_mul_I, mul_one, Real.norm_eq_abs,
    abs_of_nonneg (primeWeightSeries_nonneg sigma n)]
  exact le_rfl

theorem primeTerm_re (sigma t frequency : ℝ) (n : ℕ) :
    (primeTerm sigma t frequency n).re = cosTerm sigma t frequency n := by
  simp only [primeTerm, cosTerm, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, Complex.exp_ofReal_mul_I_re,
    Real.cos_neg]

theorem primeSeries_re (sigma t frequency : ℝ) (hsigma : 1 < sigma) :
    (primeSeries sigma t frequency).re = cosMoment sigma t frequency := by
  rw [primeSeries, Complex.re_tsum (primeTerm_summable sigma t frequency hsigma)]
  unfold cosMoment
  apply tsum_congr
  intro n
  exact primeTerm_re sigma t frequency n

/-- On every prime the phase representation equals the usual Dirichlet term. -/
theorem primeTerm_eq_dirichlet (sigma t frequency : ℝ) (n : ℕ)
    (hp : Nat.Prime n) :
    primeTerm sigma t frequency n =
      (Real.log (n : ℝ) : ℂ) * (n : ℂ) ^
        (-((sigma : ℂ) + ((frequency * t : ℝ) : ℂ) * Complex.I)) := by
  have hn : (n : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [Complex.cpow_def_of_ne_zero hn]
  have hlog : Complex.log (n : ℂ) = (Real.log (n : ℝ) : ℂ) := by
    simpa using (Complex.ofReal_log (show (0 : ℝ) ≤ (n : ℝ) by positivity)).symm
  rw [hlog]
  have hsplit : (Real.log (n : ℝ) : ℂ) *
      (-((sigma : ℂ) + ((frequency * t : ℝ) : ℂ) * Complex.I)) =
      ((-sigma * Real.log (n : ℝ) : ℝ) : ℂ) +
      (((-(frequency * (t * Real.log (n : ℝ))) : ℝ) : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [hsplit, Complex.exp_add, ← Complex.ofReal_exp]
  simp only [primeTerm, primeWeightSeries, hp, if_true,
    HVRPrimeGram.primeWeight, Complex.ofReal_mul]
  ring

/-- The Dirichlet term vanishes off the primes. -/
theorem primeTerm_eq_dirichlet_indicator (sigma t frequency : ℝ) (n : ℕ) :
    primeTerm sigma t frequency n =
      if Nat.Prime n then
        (Real.log (n : ℝ) : ℂ) * (n : ℂ) ^
          (-((sigma : ℂ) + ((frequency * t : ℝ) : ℂ) * Complex.I))
      else 0 := by
  by_cases hp : Nat.Prime n
  · simp only [hp, if_true]
    exact primeTerm_eq_dirichlet sigma t frequency n hp
  · simp [primeTerm, primeWeightSeries, hp]

/-- This exact sum is the ordinary complex prime Dirichlet series. -/
theorem primeSeries_eq_dirichlet (sigma t frequency : ℝ) :
    primeSeries sigma t frequency =
      ∑' n : ℕ, if Nat.Prime n then
        (Real.log (n : ℝ) : ℂ) * (n : ℂ) ^
          (-((sigma : ℂ) + ((frequency * t : ℝ) : ℂ) * Complex.I))
      else 0 := by
  unfold primeSeries
  apply tsum_congr
  intro n
  exact primeTerm_eq_dirichlet_indicator sigma t frequency n

/-- The infinite Gram inequality in terms of the actual complex prime series. -/
theorem infinite_complex_gram_nonnegative (sigma t : ℝ) (hsigma : 1 < sigma) :
    0 ≤ 3 * primeMass sigma + 4 * (primeSeries sigma t 1).re +
      (primeSeries sigma t 2).re := by
  rw [primeSeries_re sigma t 1 hsigma, primeSeries_re sigma t 2 hsigma]
  exact infinite_prime_gram_nonnegative sigma t hsigma

end HVRPrimeComplex
