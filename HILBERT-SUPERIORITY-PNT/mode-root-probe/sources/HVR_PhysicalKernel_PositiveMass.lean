import HVR_PhysicalKernel_Candidate
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

noncomputable section
open MeasureTheory

/-!
Uncompiled candidate for discharging the normalization condition. This stage is
separate so that any elaboration failure does not conceal the kernel candidate.
It does not assert Fourier support of the squared kernel or prove PNT.
-/
namespace HVRPhysicalKernelCandidate

open HVRSmoothingFrequencySeed

theorem wave_at_zero (w : ℝ) (hw : 0 < w) : wave w hw 0 = 1 := by
  have hreal :
      (∫ x : ℝ, (seed w hw x : ℂ)) =
        (((∫ x : ℝ, seed w hw x) : ℝ) : ℂ) := integral_complex_ofReal
  calc
    wave w hw 0 = FourierTransformInv.fourierInv (⇑(seedSchwartz w hw)) 0 := by
      change (⇑(FourierTransformInv.fourierInv (seedSchwartz w hw))) 0 = _
      rw [SchwartzMap.fourierInv_coe]
    _ = ∫ x : ℝ, (seed w hw x : ℂ) := by
      simp [Real.fourierInv_eq', seedSchwartz_apply]
    _ = 1 := by rw [hreal, seed_integral]; norm_num

theorem rawKernel_at_zero (w : ℝ) (hw : 0 < w) : rawKernel w hw 0 = 1 := by
  simp [rawKernel, wave_at_zero]

theorem mass_pos (w : ℝ) (hw : 0 < w) : 0 < mass w hw := by
  unfold mass
  apply integral_pos_of_integrable_nonneg_nonzero
    (rawKernel_continuous w hw) (rawKernel_integrable w hw)
  · intro x
    exact rawKernel_nonneg w hw x
  · exact (by rw [rawKernel_at_zero]; norm_num : rawKernel w hw 0 ≠ 0)

theorem normalizedKernel_nonneg_unconditional (w : ℝ) (hw : 0 < w) (x : ℝ) :
    0 ≤ normalizedKernel w hw x :=
  normalizedKernel_nonneg w hw (mass_pos w hw) x

theorem normalizedKernel_integral_unconditional (w : ℝ) (hw : 0 < w) :
    (∫ x : ℝ, normalizedKernel w hw x) = 1 :=
  normalizedKernel_integral w hw (mass_pos w hw)

end HVRPhysicalKernelCandidate
