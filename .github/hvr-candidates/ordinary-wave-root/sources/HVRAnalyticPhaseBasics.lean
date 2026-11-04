import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic

/-! Standalone phase and one-variable L1/Fourier estimates. The statements
are adapted from the project's previously audited frequency-bound helpers.
This module does not import prime-density, zeta or Fubini project files.
External compilation, axiom audits and swap tracing are still required. -/

noncomputable section
open Filter MeasureTheory

namespace HVRAnalyticPhaseBasics

def phase (t u : ℝ) : ℂ :=
  Complex.exp (Complex.I * ((-t * u : ℝ) : ℂ))

theorem phase_symm (t u : ℝ) : phase t u = phase u t := by
  unfold phase
  congr 2
  push_cast
  ring

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

theorem phase_mul_integrable {μ : Measure ℝ} (f : ℝ → ℂ) (u : ℝ)
    (hf : Integrable f μ) : Integrable (fun t : ℝ => f t * phase t u) μ := by
  have hp : Continuous (fun t : ℝ => phase t u) := by
    unfold phase
    fun_prop
  have hmeas : AEStronglyMeasurable (fun t : ℝ => f t * phase t u) μ :=
    hf.aestronglyMeasurable.mul hp.measurable.aestronglyMeasurable
  apply Integrable.mono' hf.norm hmeas
  filter_upwards [] with t
  have hnorm : ‖phase t u‖ = 1 := by
    simp [phase, Complex.norm_exp, Complex.mul_re, Complex.mul_im]
  simp only [norm_mul, hnorm, mul_one, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _), le_refl]

theorem integral_phase_frequency_lipschitz
    {μ : Measure ℝ} (f : ℝ → ℂ) (t r : ℝ)
    (ht : Integrable (fun u : ℝ => f u * phase t u) μ)
    (hr : Integrable (fun u : ℝ => f u * phase r u) μ)
    (hw : Integrable (fun u : ℝ => |u| * ‖f u‖) μ) :
    ‖(∫ u : ℝ, f u * phase t u ∂μ) -
        (∫ u : ℝ, f u * phase r u ∂μ)‖ ≤
      |t - r| * ∫ u : ℝ, |u| * ‖f u‖ ∂μ := by
  rw [← integral_sub ht hr]
  calc
    ‖∫ u : ℝ, (f u * phase t u - f u * phase r u) ∂μ‖ ≤
        ∫ u : ℝ, |t - r| * (|u| * ‖f u‖) ∂μ := by
      apply norm_integral_le_of_norm_le (hw.const_mul |t - r|)
      filter_upwards [] with u
      calc
        ‖f u * phase t u - f u * phase r u‖ =
            ‖f u‖ * ‖phase t u - phase r u‖ := by
          rw [← mul_sub, norm_mul]
        _ ≤ ‖f u‖ * (|t - r| * |u|) :=
          mul_le_mul_of_nonneg_left (phase_frequency_lipschitz t r u) (norm_nonneg _)
        _ = |t - r| * (|u| * ‖f u‖) := by ring
    _ = |t - r| * ∫ u : ℝ, |u| * ‖f u‖ ∂μ := integral_const_mul _ _

end HVRAnalyticPhaseBasics
