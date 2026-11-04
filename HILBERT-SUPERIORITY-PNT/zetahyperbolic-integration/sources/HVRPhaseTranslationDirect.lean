import HVRPrimeLeftQuadrature
import Mathlib.MeasureTheory.Group.Integral

/-!
One-variable change-of-variables ingredients for the finite-grid
autocorrelation/Fourier-square route. These statements do not use a product
integral or assert the Fourier convolution theorem. External cached Lean
compilation, theorem-level axiom audits and dependency traces are required.
-/

noncomputable section
open Filter MeasureTheory
open HVRZetaHyperbolicFrequencyBounds

namespace HVRPhaseTranslationDirect

/-- The real Fourier phase factors over sums. -/
theorem phase_add (s t x : ℝ) : phase (s + t) x = phase s x * phase t x := by
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Modulated translation is evaluated using one real change of variables. -/
theorem translated_phase_integral (f : ℝ → ℂ) (s x : ℝ) :
    (∫ t : ℝ, f (t - s) * phase t x) =
      phase s x * ∫ t : ℝ, f t * phase t x := by
  let g : ℝ → ℂ := fun v => f v * phase (v + s) x
  calc
    (∫ t : ℝ, f (t - s) * phase t x) = ∫ t : ℝ, g (t - s) := by
      apply integral_congr_ae
      filter_upwards [] with t
      simp only [g, sub_add_cancel]
    _ = ∫ t : ℝ, g t := integral_sub_right_eq_self g s (μ := volume)
    _ = (∫ t : ℝ, f t * phase t x) * phase s x := by
      simp_rw [g, phase_add, ← mul_assoc]
      rw [integral_mul_const]
    _ = phase s x * ∫ t : ℝ, f t * phase t x := mul_comm _ _

end HVRPhaseTranslationDirect
