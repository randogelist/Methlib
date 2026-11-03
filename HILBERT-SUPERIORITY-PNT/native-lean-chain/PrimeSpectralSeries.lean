import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Tactic
import PrimeSpectralTheta

/-!
The diagonal coefficients of the prime spectral model. The last theorem
reuses Mathlib's existing von Mangoldt / zeta logarithmic-derivative theorem;
it is a baseline bridge, not an independent derivation of that input. The
series theorem is not yet an identification with an actual Hilbert-space
operator or with the existing PNT proof chain.
-/

noncomputable section

namespace PrimeSpectralSeries

def mangoldt (n : ℕ) : ℝ := ArithmeticFunction.vonMangoldt n

def weight (sigma : ℝ) (n : ℕ) : ℝ :=
  mangoldt n * Real.exp (-sigma * Real.log (n : ℝ))

def vector (sigma : ℝ) (n : ℕ) : ℝ := PrimeSpectralTheta.amplitude sigma n

def heatTerm (sigma t : ℝ) (n : ℕ) : ℝ :=
  (vector sigma n) ^ 2 * Real.exp (-t * Real.log (n : ℝ))

theorem weight_nonneg (sigma : ℝ) (n : ℕ) : 0 ≤ weight sigma n := by
  exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.exp_nonneg _)

theorem vector_sq (sigma : ℝ) (n : ℕ) :
    (vector sigma n) ^ 2 = weight sigma n := by
  have harg : -(sigma * Real.log (n : ℝ)) / 2 +
      -(sigma * Real.log (n : ℝ)) / 2 = -sigma * Real.log (n : ℝ) := by ring
  have hexp : (Real.exp (-(sigma * Real.log (n : ℝ)) / 2)) ^ 2 =
      Real.exp (-sigma * Real.log (n : ℝ)) := by
    rw [pow_two, ← Real.exp_add, harg]
  unfold vector PrimeSpectralTheta.amplitude weight mangoldt
  rw [mul_pow, Real.sq_sqrt ArithmeticFunction.vonMangoldt_nonneg, hexp]

/-- The heat and theta constructions use the same coordinate vector. -/
theorem vector_eq_amplitude (sigma : ℝ) (n : ℕ) :
    vector sigma n = PrimeSpectralTheta.amplitude sigma n := rfl

theorem heatTerm_eq_dirichlet (sigma t : ℝ) (n : ℕ) :
    heatTerm sigma t n =
      mangoldt n * Real.exp (-(sigma + t) * Real.log (n : ℝ)) := by
  unfold heatTerm
  rw [vector_sq]
  unfold weight
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- This identifies each real diagonal heat coefficient with the L-series term. -/
theorem heatTerm_eq_LSeries_term (sigma t : ℝ) (n : ℕ) :
    (heatTerm sigma t n : ℂ) =
      LSeries.term (fun k : ℕ => (mangoldt k : ℂ))
        (((sigma + t : ℝ) : ℂ)) n := by
  rw [heatTerm_eq_dirichlet]
  have hzero : (fun k : ℕ => (mangoldt k : ℂ)) 0 = 0 := by
    simp [mangoldt]
  rw [LSeries.term_def₀ hzero]
  by_cases hn : n = 0
  · subst n
    simp [mangoldt]
  · have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    rw [Complex.cpow_def_of_ne_zero hnc]
    have hlog : Complex.log (n : ℂ) = (Real.log (n : ℝ) : ℂ) := by
      simpa using (Complex.ofReal_log (show (0 : ℝ) ≤ (n : ℝ) by positivity)).symm
    rw [hlog]
    have hexp : (Real.log (n : ℝ) : ℂ) * (-(((sigma + t : ℝ) : ℂ))) =
        ((-(sigma + t) * Real.log (n : ℝ) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hexp, ← Complex.ofReal_exp]
    simp only [Complex.ofReal_mul]

theorem heat_summable (sigma t : ℝ) (hsigma : 1 < sigma) (ht : 0 ≤ t) :
    Summable (fun n : ℕ => (heatTerm sigma t n : ℂ)) := by
  have hsreal : 1 < sigma + t := lt_of_lt_of_le hsigma (le_add_of_nonneg_right ht)
  have hs : 1 < (((sigma + t : ℝ) : ℂ)).re := by simpa using hsreal
  have hm : LSeriesSummable (fun n : ℕ => (mangoldt n : ℂ))
      (((sigma + t : ℝ) : ℂ)) := by
    apply ArithmeticFunction.LSeriesSummable_vonMangoldt
    exact hs
  change Summable (fun n : ℕ =>
    LSeries.term (fun k : ℕ => (mangoldt k : ℂ)) (((sigma + t : ℝ) : ℂ)) n) at hm
  simpa only [heatTerm_eq_LSeries_term] using hm

/-- The prime spectral vector has finite squared norm. -/
theorem vector_sq_summable (sigma : ℝ) (hsigma : 1 < sigma) :
    Summable (fun n : ℕ => (vector sigma n) ^ 2) := by
  have hc := heat_summable sigma 0 hsigma (le_refl 0)
  have hr : Summable (fun n : ℕ => heatTerm sigma 0 n) :=
    Complex.summable_ofReal.mp hc
  simpa [heatTerm] using hr

/-- Convergent diagonal series for actual zeta; this uses the existing Mathlib bridge. -/
theorem heat_hasSum_actual_zeta (sigma t : ℝ) (hsigma : 1 < sigma) (ht : 0 ≤ t) :
    HasSum (fun n : ℕ => (heatTerm sigma t n : ℂ))
      (-deriv riemannZeta (((sigma + t : ℝ) : ℂ)) /
        riemannZeta (((sigma + t : ℝ) : ℂ))) := by
  have hsreal : 1 < sigma + t := lt_of_lt_of_le hsigma (le_add_of_nonneg_right ht)
  have hs : 1 < (((sigma + t : ℝ) : ℂ)).re := by simpa using hsreal
  have hsum : (∑' n : ℕ, (heatTerm sigma t n : ℂ)) =
      -deriv riemannZeta (((sigma + t : ℝ) : ℂ)) /
        riemannZeta (((sigma + t : ℝ) : ℂ)) := by
    calc
      _ = LSeries (fun n : ℕ => (mangoldt n : ℂ)) (((sigma + t : ℝ) : ℂ)) := by
        unfold LSeries
        apply tsum_congr
        intro n
        exact heatTerm_eq_LSeries_term sigma t n
      _ = _ := by
        exact ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs
  rw [← hsum]
  exact (heat_summable sigma t hsigma ht).hasSum

end PrimeSpectralSeries
