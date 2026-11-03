import HVR_PhysicalKernel_WindowAlgebra
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Group.Integral

noncomputable section
open MeasureTheory HVRPhysicalKernelCandidate HVRPhysicalKernelWindowAlgebra

/-!
Candidate normalized affine rescaling of the actual physical kernel. This does
not yet establish tail concentration, Fourier support, or smoothing limits.
The pinned API must be checked by the external Lean build; no local Lean was run.
-/
namespace HVRPhysicalKernelScaledTranslate

def scaledTranslate (w : ℝ) (hw : 0 < w) (N c x : ℝ) : ℝ :=
  N * normalizedKernel w hw (N * (x - c))

theorem scaledTranslate_nonneg (w : ℝ) (hw : 0 < w) (N c x : ℝ)
    (hN : 0 < N) : 0 ≤ scaledTranslate w hw N c x := by
  exact mul_nonneg (le_of_lt hN) (normalizedKernel_nonneg_unconditional w hw _)

theorem scaledTranslate_integrable (w : ℝ) (hw : 0 < w) (N c : ℝ)
    (hN : 0 < N) : Integrable (scaledTranslate w hw N c) volume := by
  have hscale := (normalizedKernel_integrable w hw).comp_mul_left' (ne_of_gt hN)
  have hshift := hscale.comp_sub_right c
  change Integrable (fun x : ℝ => N * normalizedKernel w hw (N * (x - c))) volume
  exact hshift.const_mul N

theorem scaledTranslate_integral (w : ℝ) (hw : 0 < w) (N c : ℝ)
    (hN : 0 < N) : (∫ x : ℝ, scaledTranslate w hw N c x) = 1 := by
  unfold scaledTranslate
  rw [integral_const_mul]
  rw [integral_sub_right_eq_self (fun x : ℝ => normalizedKernel w hw (N * x)) c]
  rw [Measure.integral_comp_mul_left]
  simp only [abs_of_pos (inv_pos.mpr hN), smul_eq_mul,
    normalizedKernel_integral_unconditional w hw, mul_one]
  exact mul_inv_cancel₀ (ne_of_gt hN)

end HVRPhysicalKernelScaledTranslate
