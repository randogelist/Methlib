import HVRZetaHyperbolicFiniteFrequency
import NativeDominatedLimit
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
Candidate quantitative ingredient for finite-frequency approximation.

This file proves a pointwise phase Lipschitz estimate and transfers it to a
one-dimensional weighted integral. The weighted moment and both oscillatory
integrabilities remain explicit hypotheses. Finite frequency partitions,
existence of the moment for the actual prime density, and the two continuous
frequency approximation limits are not proved here.

This is source only: no external Lean compilation, axiom audit or dependency
trace has been performed for this file.
-/

noncomputable section
open Filter MeasureTheory
open scoped Topology

namespace HVRZetaHyperbolicFrequencyBounds

/-- The Fourier phase used for the positive-half-line Laplace transform. -/
def phase (t u : ℝ) : ℂ :=
  Complex.exp (Complex.I * ((-t * u : ℝ) : ℂ))

/-- The phase changes at most linearly with the frequency. -/
theorem phase_frequency_lipschitz (t r u : ℝ) :
    ‖phase t u - phase r u‖ ≤ |t - r| * |u| := by
  have hexp :
      Complex.I * ((-t * u : ℝ) : ℂ) =
        Complex.I * ((-r * u : ℝ) : ℂ) +
          Complex.I * (((r - t) * u : ℝ) : ℂ) := by
    push_cast
    ring
  have hphase : phase t u =
      phase r u * Complex.exp (Complex.I * (((r - t) * u : ℝ) : ℂ)) := by
    unfold phase
    rw [hexp, Complex.exp_add]
  have hnorm : ‖phase r u‖ = 1 := by
    simp [phase, Complex.norm_exp, Complex.mul_re, Complex.mul_im]
  calc
    ‖phase t u - phase r u‖ =
        ‖phase r u *
          (Complex.exp (Complex.I * (((r - t) * u : ℝ) : ℂ)) - 1)‖ := by
      rw [hphase]
      congr 1
      ring
    _ = ‖Complex.exp (Complex.I * (((r - t) * u : ℝ) : ℂ)) - 1‖ := by
      rw [norm_mul, hnorm, one_mul]
    _ ≤ |t - r| * |u| := by
      simpa only [Real.norm_eq_abs, abs_mul, abs_sub_comm] using
        (Real.norm_exp_I_mul_ofReal_sub_one_le (x := (r - t) * u))

/-- Weighted frequency continuity of a scalar Fourier--Laplace integral.

This result is abstract in the measure: the actual prime application must
still establish the hypotheses for its half-line damped error.
-/
theorem integral_phase_frequency_lipschitz
    {μ : Measure ℝ} (f : ℝ → ℂ) (t r : ℝ)
    (ht : Integrable (fun u : ℝ => f u * phase t u) μ)
    (hr : Integrable (fun u : ℝ => f u * phase r u) μ)
    (hw : Integrable (fun u : ℝ => |u| * ‖f u‖) μ) :
    ‖(∫ u : ℝ, f u * phase t u ∂μ) -
        (∫ u : ℝ, f u * phase r u ∂μ)‖ ≤
      |t - r| * ∫ u : ℝ, |u| * ‖f u‖ ∂μ := by
  apply HVRNativeDominatedLimit.integral_error_le_weighted |t - r| ht hr hw
  apply Filter.Eventually.of_forall
  intro u
  calc
    ‖f u * phase t u - f u * phase r u‖ =
        ‖f u‖ * ‖phase t u - phase r u‖ := by
      rw [← mul_sub, norm_mul]
    _ ≤ ‖f u‖ * (|t - r| * |u|) :=
      mul_le_mul_of_nonneg_left (phase_frequency_lipschitz t r u) (norm_nonneg _)
    _ = |t - r| * (|u| * ‖f u‖) := by ring

end HVRZetaHyperbolicFrequencyBounds

