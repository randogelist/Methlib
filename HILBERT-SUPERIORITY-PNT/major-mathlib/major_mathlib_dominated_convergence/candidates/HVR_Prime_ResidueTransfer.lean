import HVR_Zeta_CorrectionIdentity
import HVR_Prime_BoundaryBridge

noncomputable section

/-!
Conditional transfer of a normalized zeta logarithmic-derivative limit to
the corresponding actual prime cosine moment. The limit of the correction
and the zeta limit are explicit hypotheses. No zeta residue or boundary
nonvanishing is assumed to have been established here. This is a candidate
until the external Lean build and theorem-level axiom audit pass.
-/
namespace HVRPrimeResidueTransfer

open Filter HVRPrimeComplex HVRPrimeInfinite HVRPrimeZetaSplit
open HVRPowerCorrectionHolomorphic HVRZetaCorrectionIdentity

/-- Shift of the frequency into the real ordinate. -/
theorem cosMoment_frequency_one (sigma t frequency : ℝ) :
    cosMoment sigma (frequency * t) 1 = cosMoment sigma t frequency := by
  unfold cosMoment
  apply tsum_congr
  intro n
  simp only [cosTerm, one_mul, mul_assoc]

/-- The zero-ordinate cosine moment is the prime mass. -/
theorem cosMoment_zero_eq_primeMass (sigma : ℝ) :
    cosMoment sigma 0 1 = primeMass sigma := by
  simp [cosMoment, cosTerm, primeMass]

/-- The actual split transfers a normalized log-derivative limit to the
complex prime series, provided the normalized correction tends to zero. -/
theorem primeSeries_limit_of_log_derivative
    (sigma delta : ℕ → ℝ) (t : ℝ) (L : ℂ)
    (hsigma : ∀ n, 1 < sigma n)
    (hzeta : Tendsto (fun n => (delta n : ℂ) *
      (-deriv riemannZeta (zetaPoint (sigma n) t) /
        riemannZeta (zetaPoint (sigma n) t))) atTop (nhds L))
    (hcorrection : Tendsto (fun n => (delta n : ℂ) *
      complexCorrection (zetaPoint (sigma n) t)) atTop (nhds 0)) :
    Tendsto (fun n => (delta n : ℂ) * primeSeries (sigma n) t 1)
      atTop (nhds L) := by
  have heq : (fun n => (delta n : ℂ) * primeSeries (sigma n) t 1) =
      (fun n => (delta n : ℂ) *
        (-deriv riemannZeta (zetaPoint (sigma n) t) /
          riemannZeta (zetaPoint (sigma n) t)) -
        (delta n : ℂ) * complexCorrection (zetaPoint (sigma n) t)) := by
    funext n
    rw [zeta_log_deriv_eq_primeSeries_add_complexCorrection
      (sigma n) t (hsigma n)]
    ring
  rw [heq]
  simpa only [Pi.sub_apply, sub_zero] using hzeta.sub hcorrection

/-- The same transfer for the real prime cosine moment at an arbitrary
frequency. The zeta ordinate is explicitly frequency times t. -/
theorem cosMoment_limit_of_log_derivative
    (sigma delta : ℕ → ℝ) (t frequency : ℝ) (L : ℂ)
    (hsigma : ∀ n, 1 < sigma n)
    (hzeta : Tendsto (fun n => (delta n : ℂ) *
      (-deriv riemannZeta (zetaPoint (sigma n) (frequency * t)) /
        riemannZeta (zetaPoint (sigma n) (frequency * t)))) atTop (nhds L))
    (hcorrection : Tendsto (fun n => (delta n : ℂ) *
      complexCorrection (zetaPoint (sigma n) (frequency * t))) atTop (nhds 0)) :
    Tendsto (fun n => delta n * cosMoment (sigma n) t frequency)
      atTop (nhds L.re) := by
  have hp := primeSeries_limit_of_log_derivative sigma delta (frequency * t)
    L hsigma hzeta hcorrection
  have hre := (Complex.continuous_re.tendsto L).comp hp
  have heq :
      (fun n => ((delta n : ℂ) * primeSeries (sigma n) (frequency * t) 1).re) =
      (fun n => delta n * cosMoment (sigma n) t frequency) := by
    funext n
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      primeSeries_re (sigma n) (frequency * t) 1 (hsigma n),
      cosMoment_frequency_one]
  change Tendsto (fun n : ℕ =>
    ((delta n : ℂ) * primeSeries (sigma n) (frequency * t) 1).re)
      atTop (nhds L.re) at hre
  rw [heq] at hre
  exact hre

/-- Zero ordinate gives the corresponding transfer for prime mass. -/
theorem primeMass_limit_of_log_derivative
    (sigma delta : ℕ → ℝ) (L : ℂ)
    (hsigma : ∀ n, 1 < sigma n)
    (hzeta : Tendsto (fun n => (delta n : ℂ) *
      (-deriv riemannZeta (zetaPoint (sigma n) 0) /
        riemannZeta (zetaPoint (sigma n) 0))) atTop (nhds L))
    (hcorrection : Tendsto (fun n => (delta n : ℂ) *
      complexCorrection (zetaPoint (sigma n) 0)) atTop (nhds 0)) :
    Tendsto (fun n => delta n * primeMass (sigma n)) atTop (nhds L.re) := by
  have h := cosMoment_limit_of_log_derivative sigma delta 0 1 L hsigma
    (by simpa only [mul_zero] using hzeta)
    (by simpa only [mul_zero] using hcorrection)
  simpa only [cosMoment_zero_eq_primeMass] using h

end HVRPrimeResidueTransfer
