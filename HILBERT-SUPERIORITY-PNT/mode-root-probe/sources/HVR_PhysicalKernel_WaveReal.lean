import HVR_PhysicalKernel_Candidate
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Group.Integral

noncomputable section
open MeasureTheory HVRSmoothingFrequencySeed HVRPhysicalKernelCandidate

/-! Candidate realness of the physical wave from the real even seed. The
argument conjugates the Fourier integral and changes u to -u. No Lean run
was performed locally. -/
namespace HVRPhysicalKernelWaveReal

theorem wave_im_zero (w : ℝ) (hw : 0 < w) (x : ℝ) :
    (wave w hw x).im = 0 := by
  let f : ℝ → ℂ := fun u =>
    Complex.exp (((2 * Real.pi * (u * x) : ℝ) : ℂ) * Complex.I) * (seed w hw u : ℂ)
  have hwave : wave w hw x = ∫ u : ℝ, f u := by
    change (⇑(FourierTransformInv.fourierInv (seedSchwartz w hw))) x = _
    rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq']
    simp only [Real.inner_apply, smul_eq_mul, seedSchwartz_apply, f]
  have hpoint (u : ℝ) : (starRingEnd ℂ) (f u) = f (-u) := by
    have hphase : (starRingEnd ℂ)
        (((2 * Real.pi * (u * x) : ℝ) : ℂ) * Complex.I) =
        (((2 * Real.pi * ((-u) * x) : ℝ) : ℂ) * Complex.I) := by
      simp only [map_mul, Complex.conj_ofReal, Complex.conj_I,
        Complex.ofReal_mul, Complex.ofReal_neg]
      ring
    dsimp only [f]
    rw [map_mul, ← Complex.exp_conj, hphase, Complex.conj_ofReal, seed_even]
  have hstar : (starRingEnd ℂ) (∫ u : ℝ, f u) = ∫ u : ℝ, f u := by
    rw [← integral_conj]
    calc
      (∫ u : ℝ, (starRingEnd ℂ) (f u)) = ∫ u : ℝ, f (-u) := by
        apply integral_congr_ae
        filter_upwards [] with u
        exact hpoint u
      _ = ∫ u : ℝ, f u := by rw [integral_neg_eq_self]
  have hi := congrArg Complex.im hstar
  rw [← hwave] at hi
  simp only [Complex.conj_im] at hi
  linarith

end HVRPhysicalKernelWaveReal
