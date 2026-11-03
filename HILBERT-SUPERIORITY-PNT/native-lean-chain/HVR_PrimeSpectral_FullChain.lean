import HVR_PrimeDensity_FinalRoot
import HVR_PrimeLogDensity
import HVR_PrimeCount_GrowthCandidate
import PrimeSpectralOperators

/-!
Spectral links to the existing HVR prime-density chain.

The final theorem transfers the existing HVR theta-ratio theorem to the actual
prime-Hilbert-space cutoff matrix element. It is not an independent replacement
of the HVR analytic proof. The heat link uses the existing log-derivative
identification on each side and retains the prime-power correction term.

This file is proposed source; its own compilation and axiom audit have not been
performed. The existing Mathlib dependencies have not been eliminated.
-/

noncomputable section

open Filter
open scoped Topology
open PrimeSpectralHilbert PrimeSpectralOperators

namespace HVRPrimeSpectralFullChain

/-- The finite spectral cutoff and the complex prime sum in the HVR Mellin
chain are the same quantity. -/
theorem cutoff_eq_hvr_primeTheta (sigma x : ℝ) (hsigma : 1 < sigma) :
    (inner ℝ (actualPrimeVector sigma hsigma)
      (finiteDiagonal ((Finset.Ioc 0 ⌊x⌋₊).filter Nat.Prime)
        (PrimeSpectralTheta.unweight sigma) (actualPrimeVector sigma hsigma)) : ℂ) =
      HVRPrimeCountMellin.primeTheta x := by
  rw [PrimeSpectralHilbert.theta_matrix_element]
  exact (HVRPrimeCountGrowth.primeTheta_eq_chebyshev x).symm

/-- The spectral cutoff at exp t is exactly the real prime mass used by the
existing logarithmic-density argument. -/
theorem cutoff_exp_eq_hvr_logPrimeMass (sigma t : ℝ) (hsigma : 1 < sigma) :
    inner ℝ (actualPrimeVector sigma hsigma)
      (finiteDiagonal ((Finset.Ioc 0 ⌊Real.exp t⌋₊).filter Nat.Prime)
        (PrimeSpectralTheta.unweight sigma) (actualPrimeVector sigma hsigma)) =
      HVRPrimeLogDensity.logPrimeMass t := by
  simpa only [HVRPrimeLogDensity.logPrimeMass] using
    PrimeSpectralHilbert.theta_matrix_element sigma (Real.exp t) hsigma

/-- The same identification after the exponential normalization used in the
HVR smoothing chain. -/
theorem normalized_cutoff_eq_hvr_logPrimeDensity
    (sigma t : ℝ) (hsigma : 1 < sigma) :
    Real.exp (-t) *
      inner ℝ (actualPrimeVector sigma hsigma)
        (finiteDiagonal ((Finset.Ioc 0 ⌊Real.exp t⌋₊).filter Nat.Prime)
          (PrimeSpectralTheta.unweight sigma) (actualPrimeVector sigma hsigma)) =
      HVRPrimeLogDensity.logPrimeDensity t := by
  rw [cutoff_exp_eq_hvr_logPrimeMass sigma t hsigma]
  rfl

/-- The spectral heat matrix element is the same prime Mellin expression, with
its higher-prime-power correction, as in the existing HVR chain. -/
theorem heat_eq_hvr_mellin_and_correction (sigma t : ℝ)
    (hsigma : 1 < sigma) (ht : 0 ≤ t) :
    (inner ℝ (actualPrimeVector sigma hsigma)
      (heatOperator t ht (actualPrimeVector sigma hsigma)) : ℂ) =
      (((sigma + t : ℝ) : ℂ)) *
        HVRPrimeCountMellin.primeThetaMellin (((sigma + t : ℝ) : ℂ)) +
      HVRPowerCorrectionHolomorphic.complexCorrection (((sigma + t : ℝ) : ℂ)) := by
  rw [PrimeSpectralOperators.heat_matrix_element_actual_zeta sigma t hsigma ht]
  have hs : 1 < sigma + t := by linarith
  simpa only [HVRPrimeZetaSplit.zetaPoint, Complex.ofReal_zero, zero_mul, add_zero] using
    HVRPrimeCountGrowth.zeta_log_deriv_eq_primeThetaMellin_add_correction_unconditional
      (sigma + t) 0 hs

/-- The HVR smoothing argument implies convergence for the actual normalized
spectral cutoff in logarithmic coordinates. -/
theorem normalized_spectral_cutoff_tendsto_one (sigma : ℝ) (hsigma : 1 < sigma) :
    Tendsto (fun t : ℝ => Real.exp (-t) *
      inner ℝ (actualPrimeVector sigma hsigma)
        (finiteDiagonal ((Finset.Ioc 0 ⌊Real.exp t⌋₊).filter Nat.Prime)
          (PrimeSpectralTheta.unweight sigma) (actualPrimeVector sigma hsigma)))
      atTop (𝓝 1) := by
  have hfun : (fun t : ℝ => Real.exp (-t) *
      inner ℝ (actualPrimeVector sigma hsigma)
        (finiteDiagonal ((Finset.Ioc 0 ⌊Real.exp t⌋₊).filter Nat.Prime)
          (PrimeSpectralTheta.unweight sigma) (actualPrimeVector sigma hsigma))) =
      HVRPrimeLogDensity.logPrimeDensity := by
    funext t
    exact normalized_cutoff_eq_hvr_logPrimeDensity sigma t hsigma
  rw [hfun]
  exact HVRPrimeDensityConcentratedSqueeze.primeDensity_tendsto_of_concentrated_smoothing
    HVRPrimeDensityFinalRoot.actual_prime_concentrated_smoothing

/-- The existing HVR theta asymptotic, now stated for the actual spectral cutoff
matrix element. The hypothesis on sigma ensures the prime vector lies in ℓ²;
there are no additional analytic premises in the theorem statement. -/
theorem spectral_cutoff_ratio_tendsto_one (sigma : ℝ) (hsigma : 1 < sigma) :
    Tendsto (fun x : ℝ =>
      inner ℝ (actualPrimeVector sigma hsigma)
        (finiteDiagonal ((Finset.Ioc 0 ⌊x⌋₊).filter Nat.Prime)
          (PrimeSpectralTheta.unweight sigma) (actualPrimeVector sigma hsigma)) / x)
      atTop (𝓝 1) := by
  have hfun : (fun x : ℝ =>
      inner ℝ (actualPrimeVector sigma hsigma)
        (finiteDiagonal ((Finset.Ioc 0 ⌊x⌋₊).filter Nat.Prime)
          (PrimeSpectralTheta.unweight sigma) (actualPrimeVector sigma hsigma)) / x) =
      (fun x : ℝ => Chebyshev.theta x / x) := by
    funext x
    rw [PrimeSpectralHilbert.theta_matrix_element sigma x hsigma]
  rw [hfun]
  exact HVRPrimeDensityFinalRoot.theta_ratio_tendsto_one

end HVRPrimeSpectralFullChain
