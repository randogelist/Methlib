import PrimeSpectralSeries
import PrimeSpectralResolvent

noncomputable section
open MeasureTheory

/-!
Specialization of the heat/resolvent series to the von Mangoldt weights.
The zeta identification explicitly uses PrimeSpectralSeries.heat_hasSum_actual_zeta,
which in turn uses Mathlib's existing zeta logarithmic-derivative identity.
No operator-theoretic identification with an unbounded self-adjoint operator
or independent Euler-product rederivation is claimed here.
-/
namespace PrimeSpectralBridge

theorem weight_summable (sigma : ℝ) (hsigma : 1 < sigma) :
    Summable (PrimeSpectralSeries.weight sigma) := by
  have hs := PrimeSpectralSeries.vector_sq_summable sigma hsigma
  have heq : (fun n : ℕ => (PrimeSpectralSeries.vector sigma n) ^ 2) =
      PrimeSpectralSeries.weight sigma := by
    funext n
    exact PrimeSpectralSeries.vector_sq sigma n
  rw [heq] at hs
  exact hs

/-- The actual weighted prime-power heat series has the diagonal resolvent
as its Laplace integral. -/
theorem prime_heat_resolvent_laplace (sigma w : ℝ)
    (hsigma : 1 < sigma) (hw : 0 < w) :
    (∫ t : ℝ in Set.Ioi 0,
      Real.exp (-w * t) * (∑' n : ℕ, PrimeSpectralSeries.heatTerm sigma t n)) =
      ∑' n : ℕ, PrimeSpectralSeries.weight sigma n / (w + Real.log (n : ℝ)) := by
  have h := PrimeSpectralResolvent.heat_series_resolvent_of_summable_mass
      (PrimeSpectralSeries.weight sigma) (fun n : ℕ => Real.log (n : ℝ)) w hw
      (fun n => Real.log_natCast_nonneg n)
      (PrimeSpectralSeries.weight_nonneg sigma) (weight_summable sigma hsigma)
  have hterm (t : ℝ) (n : ℕ) : PrimeSpectralSeries.heatTerm sigma t n =
      PrimeSpectralSeries.weight sigma n * Real.exp (-Real.log (n : ℝ) * t) := by
    have harg : -t * Real.log (n : ℝ) = -Real.log (n : ℝ) * t := by ring
    simp only [PrimeSpectralSeries.heatTerm, PrimeSpectralSeries.vector_sq, harg]
  simpa only [hterm] using h

/-- For real positive time, the heat sum equals the real part of the actual
zeta logarithmic derivative. The proof reuses the Mathlib endpoint. -/
theorem heat_series_eq_zeta_realpart (sigma t : ℝ)
    (hsigma : 1 < sigma) (ht : 0 ≤ t) :
    (∑' n : ℕ, PrimeSpectralSeries.heatTerm sigma t n) =
      (-deriv riemannZeta (((sigma + t : ℝ) : ℂ)) /
        riemannZeta (((sigma + t : ℝ) : ℂ))).re := by
  have h := (PrimeSpectralSeries.heat_hasSum_actual_zeta sigma t hsigma ht).tsum_eq
  rw [← Complex.ofReal_tsum] at h
  have hr := congrArg Complex.re h
  simpa using hr

/-- Real-valued resolvent/Laplace identity for the actual zeta expression.
The zeta bridge reuses the named existing Mathlib theorem. -/
theorem zeta_realpart_resolvent_laplace (sigma w : ℝ)
    (hsigma : 1 < sigma) (hw : 0 < w) :
    (∫ t : ℝ in Set.Ioi 0, Real.exp (-w * t) *
      (-deriv riemannZeta (((sigma + t : ℝ) : ℂ)) /
        riemannZeta (((sigma + t : ℝ) : ℂ))).re) =
      ∑' n : ℕ, PrimeSpectralSeries.weight sigma n / (w + Real.log (n : ℝ)) := by
  calc
    (∫ t : ℝ in Set.Ioi 0, Real.exp (-w * t) *
      (-deriv riemannZeta (((sigma + t : ℝ) : ℂ)) /
        riemannZeta (((sigma + t : ℝ) : ℂ))).re) =
        ∫ t : ℝ in Set.Ioi 0,
          Real.exp (-w * t) * (∑' n : ℕ, PrimeSpectralSeries.heatTerm sigma t n) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [heat_series_eq_zeta_realpart sigma t hsigma (le_of_lt ht)]
    _ = _ := prime_heat_resolvent_laplace sigma w hsigma hw

end PrimeSpectralBridge
