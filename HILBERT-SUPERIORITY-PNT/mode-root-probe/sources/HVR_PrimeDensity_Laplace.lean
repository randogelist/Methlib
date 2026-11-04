import HVR_PrimeCount_LogSubstitution
import HVR_PrimeCount_ExpGrowth
import HVR_Complex_PoleLaplace

noncomputable section
open Filter MeasureTheory
open HVRPrimeCountMellin HVRPrimeCountLogSubstitution HVRPrimeZetaSplit
open HVRPrimeLogDensity HVRPrimeCountExpGrowth HVRSmoothingAnalyticGerms
open HVRMonotoneNormalization

/-!
Candidate actual prime-density Laplace transform. The logarithmic change of
variables and the positive real integrable majorant are prior audited edges.
This module attempts to establish complex integrability, subtract the pole
inside the integral, and identify the resulting transform with the regular
analytic expression on the half-plane. It does not establish boundary Fourier
limits, a smoothing kernel, PNT, or route independence. No Lean was run locally.
-/
namespace HVRPrimeDensityLaplace

/-- The Laplace transform of the normalized actual logarithmic prime count,
minus one, on the positive logarithmic half-line. -/
def primeDensityLaplace (z : ℂ) : ℂ :=
  ∫ u : ℝ in Set.Ioi 0,
    ((logPrimeDensity u : ℂ) - 1) * Complex.exp (-z * (u : ℂ))

/-- The exponential integral supplied by the Mellin substitution is genuinely
integrable when the real part of the original parameter exceeds one. -/
theorem primeMass_complex_integrable (sigma t : ℝ) (hsigma : 1 < sigma) :
    IntegrableOn (fun u : ℝ => primeTheta (Real.exp u) *
      Complex.exp (-(zetaPoint sigma t) * (u : ℂ))) (Set.Ioi 0) volume := by
  have hmajor : IntegrableOn (fun u : ℝ => Real.exp (-sigma * u) * logPrimeMass u)
      (Set.Ioi 0) volume := by
    apply (logPrimeMass_integrableOn_exp_neg_mul sigma hsigma).mono_set
    intro u hu
    change (0 : ℝ) < u at hu
    change (0 : ℝ) ≤ u
    exact le_of_lt hu
  have hmass : Measurable (fun u : ℝ => (logPrimeMass u : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp logPrimeMass_monotone.measurable
  have hexp : Continuous (fun u : ℝ => Complex.exp (-(zetaPoint sigma t) * (u : ℂ))) := by
    fun_prop
  have hmeas : Measurable (fun u : ℝ => (logPrimeMass u : ℂ) *
      Complex.exp (-(zetaPoint sigma t) * (u : ℂ))) :=
    hmass.mul hexp.measurable
  have hprime : IntegrableOn (fun u : ℝ => (logPrimeMass u : ℂ) *
      Complex.exp (-(zetaPoint sigma t) * (u : ℂ))) (Set.Ioi 0) volume := by
    apply Integrable.mono' hmajor hmeas.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro u
    have hn : 0 ≤ logPrimeMass u := Chebyshev.theta_nonneg (Real.exp u)
    have hr : (-(zetaPoint sigma t) * (u : ℂ)).re = -sigma * u := by
      simp [zetaPoint, Complex.mul_re] <;> ring
    calc
      ‖(logPrimeMass u : ℂ) * Complex.exp (-(zetaPoint sigma t) * (u : ℂ))‖ =
          Real.exp (-sigma * u) * logPrimeMass u := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hn,
          Complex.norm_exp, hr]
        ring
      _ ≤ _ := le_rfl
  simpa only [logPrimeMass_eq_primeTheta] using hprime

/-- The integrand of the true prime-density Laplace transform equals the
separately integrable prime term minus the exponential pole term. -/
theorem density_integrand_eq (sigma t u : ℝ) :
    ((logPrimeDensity u : ℂ) - 1) *
        Complex.exp (-(zetaPoint sigma t - 1) * (u : ℂ)) =
      primeTheta (Real.exp u) * Complex.exp (-(zetaPoint sigma t) * (u : ℂ)) -
        Complex.exp (-(zetaPoint sigma t - 1) * (u : ℂ)) := by
  have he : (Real.exp (-u) : ℂ) *
      Complex.exp (-(zetaPoint sigma t - 1) * (u : ℂ)) =
      Complex.exp (-(zetaPoint sigma t) * (u : ℂ)) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  unfold logPrimeDensity normalizedMass
  rw [Complex.ofReal_mul, logPrimeMass_eq_primeTheta]
  calc
    ((Real.exp (-u) : ℂ) * primeTheta (Real.exp u) - 1) *
        Complex.exp (-(zetaPoint sigma t - 1) * (u : ℂ)) =
      primeTheta (Real.exp u) * ((Real.exp (-u) : ℂ) *
        Complex.exp (-(zetaPoint sigma t - 1) * (u : ℂ))) -
          Complex.exp (-(zetaPoint sigma t - 1) * (u : ℂ)) := by ring
    _ = _ := by rw [he]

/-- The actual prime-density Laplace integrand is integrable on the positive
half-line for all parameters with positive real part. -/
theorem primeDensity_integrable (sigma t : ℝ) (hsigma : 1 < sigma) :
    IntegrableOn (fun u : ℝ => ((logPrimeDensity u : ℂ) - 1) *
      Complex.exp (-(zetaPoint sigma t - 1) * (u : ℂ))) (Set.Ioi 0) volume := by
  have hz : 0 < (zetaPoint sigma t - 1).re := by
    simp [zetaPoint]
    linarith
  have hprime := primeMass_complex_integrable sigma t hsigma
  have hconst := HVRComplexPoleLaplace.exponential_integrable (zetaPoint sigma t - 1) hz
  apply (hprime.sub hconst).congr
  filter_upwards [] with u
  exact (density_integrand_eq sigma t u).symm

/-- The actual normalized prime-count Laplace transform equals the regular
analytic expression for every point approached from the right half-plane. -/
theorem primeDensityLaplace_eq_regularPartAt
    (sigma t : ℝ) (hsigma : 1 < sigma) :
    primeDensityLaplace (zetaPoint sigma t - 1) =
      regularPartAt (zetaPoint sigma t) := by
  have hz : 0 < (zetaPoint sigma t - 1).re := by
    simp [zetaPoint]
    linarith
  have hprime := primeMass_complex_integrable sigma t hsigma
  have hconst : IntegrableOn (fun u : ℝ =>
      Complex.exp (-(zetaPoint sigma t - 1) * (u : ℂ))) (Set.Ioi 0) volume :=
    HVRComplexPoleLaplace.exponential_integrable _ hz
  have hpole :
      (∫ u : ℝ in Set.Ioi 0,
        Complex.exp (-(zetaPoint sigma t - 1) * (u : ℂ))) =
      (zetaPoint sigma t - 1)⁻¹ := by
    exact HVRComplexPoleLaplace.exponential_integral_eq_inv _ hz
  unfold primeDensityLaplace
  calc
    (∫ u : ℝ in Set.Ioi 0, ((logPrimeDensity u : ℂ) - 1) *
      Complex.exp (-(zetaPoint sigma t - 1) * (u : ℂ))) =
      (∫ u : ℝ in Set.Ioi 0, primeTheta (Real.exp u) *
        Complex.exp (-(zetaPoint sigma t) * (u : ℂ))) -
      (∫ u : ℝ in Set.Ioi 0,
        Complex.exp (-(zetaPoint sigma t - 1) * (u : ℂ))) := by
          rw [← integral_sub hprime hconst]
          apply integral_congr_ae
          filter_upwards [] with u
          exact density_integrand_eq sigma t u
    _ = regularPartAt (zetaPoint sigma t) := by
      rw [hpole]
      exact exp_integral_sub_pole_eq_regularPartAt sigma t hsigma

end HVRPrimeDensityLaplace
