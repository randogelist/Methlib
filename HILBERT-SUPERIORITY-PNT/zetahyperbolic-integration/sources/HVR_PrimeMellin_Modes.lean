import HVR_Zeta_CorrectionIdentity
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Tactic

noncomputable section

open MeasureTheory Filter
open HVRPrimeComplex HVRPrimeZetaSplit

/-!
Prime-specific Laplace modes for a direct theta Mellin bridge.

The file includes candidate proofs for mode integrability and norm-integral
summability from the existing prime-weight summability theorem. Its main
remaining hypothesis is the actual theta-exponential/mode-sum identification
almost everywhere; the exponential change of variables is also separate.
All results require external compilation and theorem-level axiom audits.
The file uses integral_tsum_of_summable_integral_norm and does not establish
independence from dominated-convergence infrastructure. It is deliberately
separate from the PNT root.
-/
namespace HVRPrimeMellinModes

/-- Actual prime-supported Laplace mode on the real line. -/
def primeMode (s : ℂ) (n : ℕ) : ℝ → ℂ :=
  if Nat.Prime n then
    (Set.Ioi (Real.log (n : ℝ))).indicator
      (fun u : ℝ => (Real.log (n : ℝ) : ℂ) *
        Complex.exp (-s * (u : ℂ)))
  else 0

/-- The integral of one mode on its own half-line. -/
theorem weighted_exponential_mode (s : ℂ) (a : ℝ) (c : ℂ) (hs : 0 < s.re) :
    (∫ u : ℝ in Set.Ioi a, c * Complex.exp (-s * (u : ℂ))) =
      c * Complex.exp (-s * (a : ℂ)) / s := by
  have hz : (-s).re < 0 := by simpa using neg_neg_of_pos hs
  rw [integral_const_mul, integral_exp_mul_complex_Ioi hz]
  simp only [neg_div_neg_eq]
  ring

/-- The exact integral of the prime-supported mode, before rewriting it as
the prime Dirichlet coefficient. -/
theorem primeMode_integral (s : ℂ) (n : ℕ) (hs : 0 < s.re) :
    (∫ u : ℝ, primeMode s n u) =
      if Nat.Prime n then
        (Real.log (n : ℝ) : ℂ) *
          Complex.exp (-s * (Real.log (n : ℝ) : ℂ)) / s
      else 0 := by
  by_cases hp : Nat.Prime n
  · simp only [primeMode, hp, if_true, integral_indicator measurableSet_Ioi]
    exact weighted_exponential_mode s (Real.log (n : ℝ)) (Real.log (n : ℝ) : ℂ) hs
  · simp [primeMode, hp]

/-- Every individual prime mode is integrable. -/
theorem primeMode_integrable (s : ℂ) (n : ℕ) (hs : 0 < s.re) :
    Integrable (primeMode s n) volume := by
  by_cases hp : Nat.Prime n
  · simp only [primeMode, hp, if_true]
    rw [integrable_indicator_iff measurableSet_Ioi]
    have hz : (-s).re < 0 := by simpa using neg_neg_of_pos hs
    exact (integrableOn_exp_mul_complex_Ioi hz (Real.log (n : ℝ))).const_mul _
  · simp [primeMode, hp]

/-- The integrated norm is the existing prime weight divided by sigma. -/
theorem primeMode_integral_norm (sigma t : ℝ) (n : ℕ) (hsigma : 1 < sigma) :
    (∫ u : ℝ, ‖primeMode (zetaPoint sigma t) n u‖) =
      HVRPrimeSummability.primeWeightSeries sigma n / sigma := by
  by_cases hp : Nat.Prime n
  · have hn : (1 : ℝ) ≤ n := by exact_mod_cast hp.one_le
    have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn
    have hneg : -sigma < 0 := by linarith
    have hre (u : ℝ) :
        (-(zetaPoint sigma t) * (u : ℂ)).re = -sigma * u := by
      simp [zetaPoint, Complex.mul_re, Complex.neg_re]
    calc
      (∫ u : ℝ, ‖primeMode (zetaPoint sigma t) n u‖) =
          ∫ u : ℝ, (Set.Ioi (Real.log (n : ℝ))).indicator
            (fun x : ℝ => Real.log (n : ℝ) * Real.exp (-sigma * x)) u := by
        apply integral_congr_ae
        filter_upwards [] with u
        by_cases hu : u ∈ Set.Ioi (Real.log (n : ℝ))
        · simp [primeMode, hp, hu, norm_mul, Complex.norm_exp, hre,
            Real.norm_eq_abs, abs_of_nonneg hlog]
        · simp [primeMode, hp, hu]
      _ = ∫ u : ℝ in Set.Ioi (Real.log (n : ℝ)),
          Real.log (n : ℝ) * Real.exp (-sigma * u) :=
        integral_indicator measurableSet_Ioi
      _ = HVRPrimeSummability.primeWeightSeries sigma n / sigma := by
        rw [integral_const_mul, integral_exp_mul_Ioi hneg]
        simp only [neg_div_neg_eq, HVRPrimeSummability.primeWeightSeries, hp,
          if_true, HVRPrimeGram.primeWeight]
        ring
  · simp [primeMode, hp, HVRPrimeSummability.primeWeightSeries]

/-- Integrated mode norms are summable by the existing prime-weight estimate. -/
theorem primeMode_integral_norm_summable (sigma t : ℝ) (hsigma : 1 < sigma) :
    Summable (fun n : ℕ => ∫ u : ℝ, ‖primeMode (zetaPoint sigma t) n u‖) := by
  simpa only [primeMode_integral_norm sigma t _ hsigma] using
    (HVRPrimeSummability.primeWeightSeries_summable sigma hsigma).div_const sigma

/-- Each actual mode integrates to the corresponding HVR prime-series term. -/
theorem primeMode_integral_eq_primeTerm (sigma t : ℝ) (n : ℕ) (hsigma : 1 < sigma) :
    (∫ u : ℝ, primeMode (zetaPoint sigma t) n u) =
      primeTerm sigma t 1 n / zetaPoint sigma t := by
  have hs : 0 < (zetaPoint sigma t).re := by
    simp only [zetaPoint, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_self,
      add_zero]
    linarith
  rw [primeMode_integral _ _ hs]
  by_cases hp : Nat.Prime n
  · simp only [hp, if_true]
    rw [primeTerm_eq_dirichlet sigma t 1 n hp]
    have hn : (n : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hlog : Complex.log (n : ℂ) = (Real.log (n : ℝ) : ℂ) := by
      simpa using (Complex.ofReal_log (show (0 : ℝ) ≤ (n : ℝ) by positivity)).symm
    have harg :
        -(zetaPoint sigma t) * (Real.log (n : ℝ) : ℂ) =
          Complex.log (n : ℂ) *
            (-((sigma : ℂ) + ((1 * t : ℝ) : ℂ) * Complex.I)) := by
      rw [hlog]
      simp only [zetaPoint, one_mul]
      ring
    rw [harg, ← Complex.cpow_def_of_ne_zero hn]
  · simp [hp, primeTerm, HVRPrimeSummability.primeWeightSeries]

/-- Conditional direct-mode assembly. The three hypotheses are intentionally
explicit; this theorem alone does not close the prime Mellin endpoint. -/
theorem theta_exp_laplace_of_modes (sigma t : ℝ) (hsigma : 1 < sigma)
    (hi : ∀ n : ℕ, Integrable (primeMode (zetaPoint sigma t) n) volume)
    (hnorm : Summable (fun n : ℕ =>
      ∫ u : ℝ, ‖primeMode (zetaPoint sigma t) n u‖))
    (hpoint : ∀ᵐ u : ℝ ∂volume,
      (Set.Ioi (0 : ℝ)).indicator
          (fun x : ℝ => Complex.exp (-(zetaPoint sigma t) * (x : ℂ)) *
            (Chebyshev.theta (Real.exp x) : ℂ)) u =
        ∑' n : ℕ, primeMode (zetaPoint sigma t) n u) :
    (∫ u : ℝ in Set.Ioi 0,
      Complex.exp (-(zetaPoint sigma t) * (u : ℂ)) *
        (Chebyshev.theta (Real.exp u) : ℂ)) =
      primeSeries sigma t 1 / zetaPoint sigma t := by
  rw [← integral_indicator measurableSet_Ioi]
  calc
    (∫ u : ℝ, (Set.Ioi (0 : ℝ)).indicator
        (fun x : ℝ => Complex.exp (-(zetaPoint sigma t) * (x : ℂ)) *
          (Chebyshev.theta (Real.exp x) : ℂ)) u) =
        ∫ u : ℝ, ∑' n : ℕ, primeMode (zetaPoint sigma t) n u :=
      integral_congr_ae hpoint
    _ = ∑' n : ℕ, ∫ u : ℝ, primeMode (zetaPoint sigma t) n u :=
      (integral_tsum_of_summable_integral_norm hi hnorm).symm
    _ = primeSeries sigma t 1 / zetaPoint sigma t := by
      simp_rw [primeMode_integral_eq_primeTerm sigma t _ hsigma]
      unfold primeSeries
      simp only [div_eq_mul_inv, tsum_mul_right]

/-- With mode-integrability and norm-summability discharged, only the
pointwise prime/theta expansion remains as an explicit mode hypothesis. -/
theorem theta_exp_laplace_of_prime_expansion (sigma t : ℝ) (hsigma : 1 < sigma)
    (hpoint : ∀ᵐ u : ℝ ∂volume,
      (Set.Ioi (0 : ℝ)).indicator
          (fun x : ℝ => Complex.exp (-(zetaPoint sigma t) * (x : ℂ)) *
            (Chebyshev.theta (Real.exp x) : ℂ)) u =
        ∑' n : ℕ, primeMode (zetaPoint sigma t) n u) :
    (∫ u : ℝ in Set.Ioi 0,
      Complex.exp (-(zetaPoint sigma t) * (u : ℂ)) *
        (Chebyshev.theta (Real.exp u) : ℂ)) =
      primeSeries sigma t 1 / zetaPoint sigma t :=
  theta_exp_laplace_of_modes sigma t hsigma
    (fun n => primeMode_integrable _ n (by simp [zetaPoint]; linarith))
    (primeMode_integral_norm_summable sigma t hsigma) hpoint

end HVRPrimeMellinModes

