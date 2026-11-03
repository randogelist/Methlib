import HVR_PrimeCount_MellinCandidate
import Mathlib.NumberTheory.Chebyshev
import PrimeSpectralHilbert

noncomputable section
open scoped BigOperators
open Filter Asymptotics HVRPrimeCountMellin HVRPrimeZetaSplit HVRZetaLogDerivative
open HVRPowerCorrectionHolomorphic

/-! Candidate integration: identify the prime partial sums directly with the
finite Hilbert matrix element, then use the amendment's theta identity in the
existing growth proof. The growth bound remains Mathlib's Chebyshev bound.
This changed source and its downstream dependants require a fresh Lean build
and axiom audit. -/
namespace HVRPrimeCountGrowth

theorem primeTheta_eq_spectral (sigma x : ℝ) (hsigma : 1 < sigma) :
    primeTheta x =
      (inner ℝ (PrimeSpectralHilbert.actualPrimeVector sigma hsigma)
        (PrimeSpectralHilbert.finiteDiagonal
          ((Finset.Ioc 0 ⌊x⌋₊).filter Nat.Prime)
          (PrimeSpectralTheta.unweight sigma)
          (PrimeSpectralHilbert.actualPrimeVector sigma hsigma)) : ℂ) := by
  classical
  have hset : Finset.Icc 1 ⌊x⌋₊ = Finset.Ioc 0 ⌊x⌋₊ := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have hreal :
      (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, primeCoefficient n) =
        ∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter Nat.Prime,
          PrimeSpectralTheta.amplitude sigma n *
            (PrimeSpectralTheta.unweight sigma n *
              PrimeSpectralTheta.amplitude sigma n) := by
    rw [hset, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hp : Nat.Prime n
    · simp only [hp, if_true]
      simpa only [primeCoefficient, hp, if_true] using
        (PrimeSpectralTheta.prime_coordinate_cancellation sigma hp).symm
    · simp [primeCoefficient, hp]
  have hinner :
      inner ℝ (PrimeSpectralHilbert.actualPrimeVector sigma hsigma)
        (PrimeSpectralHilbert.finiteDiagonal
          ((Finset.Ioc 0 ⌊x⌋₊).filter Nat.Prime)
          (PrimeSpectralTheta.unweight sigma)
          (PrimeSpectralHilbert.actualPrimeVector sigma hsigma)) =
        ∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter Nat.Prime,
          PrimeSpectralTheta.amplitude sigma n *
            (PrimeSpectralTheta.unweight sigma n *
              PrimeSpectralTheta.amplitude sigma n) := by
    rw [PrimeSpectralHilbert.finiteDiagonal_matrix_element]
    simp only [PrimeSpectralHilbert.actualPrimeVector_apply]
  calc
    primeTheta x =
        (((∑ n ∈ Finset.Icc 1 ⌊x⌋₊, primeCoefficient n) : ℝ) : ℂ) := by
          simp only [primeTheta, primeCoefficientC, Complex.ofReal_sum]
    _ = (((∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter Nat.Prime,
          PrimeSpectralTheta.amplitude sigma n *
            (PrimeSpectralTheta.unweight sigma n *
              PrimeSpectralTheta.amplitude sigma n)) : ℝ) : ℂ) :=
        congrArg (fun z : ℝ => (z : ℂ)) hreal
    _ = _ := congrArg (fun z : ℝ => (z : ℂ)) hinner.symm

theorem primeTheta_eq_chebyshev (x : ℝ) :
    primeTheta x = (Chebyshev.theta x : ℂ) := by
  have hsigma : (1 : ℝ) < 2 := by norm_num
  calc
    primeTheta x =
        (inner ℝ (PrimeSpectralHilbert.actualPrimeVector 2 hsigma)
          (PrimeSpectralHilbert.finiteDiagonal
            ((Finset.Ioc 0 ⌊x⌋₊).filter Nat.Prime)
            (PrimeSpectralTheta.unweight 2)
            (PrimeSpectralHilbert.actualPrimeVector 2 hsigma)) : ℂ) :=
      primeTheta_eq_spectral 2 x hsigma
    _ = (Chebyshev.theta x : ℂ) :=
      congrArg (fun z : ℝ => (z : ℂ))
        (PrimeSpectralHilbert.theta_matrix_element 2 x hsigma)

/-- The actual log-prime coefficient partial sums have linear growth. -/
theorem primeCoefficient_partial_sum_isBigO :
    (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, primeCoefficientC k)
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (1 : ℝ)) := by
  apply Asymptotics.IsBigO.of_bound (Real.log 4)
  apply Filter.Eventually.of_forall
  intro n
  have hs : (∑ k ∈ Finset.Icc 1 n, primeCoefficientC k) =
      (Chebyshev.theta (n : ℝ) : ℂ) := by
    simpa only [primeTheta, Nat.floor_natCast] using primeTheta_eq_chebyshev (n : ℝ)
  rw [hs]
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  simpa only [Real.rpow_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Chebyshev.theta_nonneg (n : ℝ)),
    abs_of_nonneg hn] using
      (Chebyshev.theta_le_log4_mul_x hn)

/-- Mellin identity with no prime-count growth premise. -/
theorem primeSeries_eq_mul_primeThetaMellin_unconditional
    (sigma t : ℝ) (hsigma : 1 < sigma) :
    HVRPrimeComplex.primeSeries sigma t 1 =
      zetaPoint sigma t * primeThetaMellin (zetaPoint sigma t) := by
  exact primeSeries_eq_mul_primeThetaMellin sigma t 1 hsigma (by norm_num) hsigma
    primeCoefficient_partial_sum_isBigO

theorem zeta_log_deriv_eq_primeThetaMellin_add_correction_unconditional
    (sigma t : ℝ) (hsigma : 1 < sigma) :
    -deriv riemannZeta (zetaPoint sigma t) / riemannZeta (zetaPoint sigma t) =
      zetaPoint sigma t * primeThetaMellin (zetaPoint sigma t) +
        complexCorrection (zetaPoint sigma t) := by
  exact zeta_log_deriv_eq_primeThetaMellin_add_correction sigma t 1 hsigma
    (by norm_num) hsigma primeCoefficient_partial_sum_isBigO

end HVRPrimeCountGrowth
