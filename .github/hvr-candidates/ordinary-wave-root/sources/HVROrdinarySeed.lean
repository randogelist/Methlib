import HVR_Smoothing_FrequencySeed

/-! Minimal standalone complex seed for the ordinary physical-wave route.
This does not import a Schwartz Fourier transform, PNT, or the integral-swap
bridge. External Lean compilation and dependency auditing are still needed. -/

noncomputable section
open MeasureTheory HVRSmoothingFrequencySeed

namespace HVROrdinarySeed

def complexSeed (w : ℝ) (hw : 0 < w) : ℝ → ℂ :=
  Complex.ofReal ∘ seed w hw

theorem complexSeed_compact (w : ℝ) (hw : 0 < w) :
    HasCompactSupport (complexSeed w hw) := by
  exact (seed_compact w hw).comp_left (show Complex.ofReal 0 = 0 by simp)

theorem complexSeed_smooth (w : ℝ) (hw : 0 < w) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (complexSeed w hw) := by
  simpa only [complexSeed, Function.comp_def, Complex.ofRealCLM_apply] using
    Complex.ofRealCLM.contDiff.comp (seed_smooth_Cinfty w hw)

end HVROrdinarySeed
