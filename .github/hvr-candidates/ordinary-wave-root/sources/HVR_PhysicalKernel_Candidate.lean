import HVROrdinarySeedWaveStandalone
import HVR_Smoothing_FrequencySeed
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic

noncomputable section
open MeasureTheory

/-!
Candidate refactor: `wave` is retained as the original Schwartz-valued
declaration. `rawKernel` now uses the independently constructed ordinary
phase-integral wave, with direct one-variable continuity and integrability.
The root and named theorems require a fresh external Lean build and audit.
No dependency-independence or PNT closure claim is made by this module.
-/
namespace HVRPhysicalKernelCandidate

open HVRSmoothingFrequencySeed

def complexSeed (w : ℝ) (hw : 0 < w) : ℝ → ℂ :=
  Complex.ofReal ∘ seed w hw

theorem complexSeed_compact (w : ℝ) (hw : 0 < w) :
    HasCompactSupport (complexSeed w hw) := by
  exact (seed_compact w hw).comp_left (show Complex.ofReal 0 = 0 by simp)

theorem complexSeed_smooth (w : ℝ) (hw : 0 < w) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (complexSeed w hw) := by
  simpa only [complexSeed, Function.comp_def, Complex.ofRealCLM_apply] using
    Complex.ofRealCLM.contDiff.comp (seed_smooth_Cinfty w hw)

def seedSchwartz (w : ℝ) (hw : 0 < w) : SchwartzMap ℝ ℂ :=
  (complexSeed_compact w hw).toSchwartzMap (complexSeed_smooth w hw)

theorem seedSchwartz_apply (w : ℝ) (hw : 0 < w) (x : ℝ) :
    seedSchwartz w hw x = (seed w hw x : ℂ) := by
  simp [seedSchwartz, complexSeed]

theorem seedSchwartz_zero_of_band (w : ℝ) (hw : 0 < w) (x : ℝ)
    (hx : w / 2 ≤ |x|) : seedSchwartz w hw x = 0 := by
  rw [seedSchwartz_apply, seed_zero_of_band w hw x hx]
  norm_num

def wave (w : ℝ) (hw : 0 < w) : SchwartzMap ℝ ℂ :=
  FourierTransformInv.fourierInv (seedSchwartz w hw)

def rawKernel (w : ℝ) (hw : 0 < w) (x : ℝ) : ℝ :=
  ‖HVROrdinarySeedWave.ordinaryWave w hw x‖ ^ 2

theorem rawKernel_nonneg (w : ℝ) (hw : 0 < w) (x : ℝ) :
    0 ≤ rawKernel w hw x := by
  exact sq_nonneg _

theorem rawKernel_continuous (w : ℝ) (hw : 0 < w) :
    Continuous (rawKernel w hw) := by
  exact (HVROrdinarySeedWave.ordinaryWave_continuous w hw).norm.pow 2

theorem rawKernel_integrable (w : ℝ) (hw : 0 < w) :
    Integrable (rawKernel w hw) volume := by
  exact HVROrdinarySeedWave.ordinaryWave_norm_sq_integrable w hw

def mass (w : ℝ) (hw : 0 < w) : ℝ :=
  ∫ x : ℝ, rawKernel w hw x

def normalizedKernel (w : ℝ) (hw : 0 < w) (x : ℝ) : ℝ :=
  rawKernel w hw x / mass w hw

theorem normalizedKernel_nonneg (w : ℝ) (hw : 0 < w)
    (hmass : 0 < mass w hw) (x : ℝ) :
    0 ≤ normalizedKernel w hw x := by
  exact div_nonneg (rawKernel_nonneg w hw x) (le_of_lt hmass)

theorem normalizedKernel_integral (w : ℝ) (hw : 0 < w)
    (hmass : 0 < mass w hw) :
    (∫ x : ℝ, normalizedKernel w hw x) = 1 := by
  simp only [normalizedKernel, integral_div]
  exact div_self (ne_of_gt hmass)

end HVRPhysicalKernelCandidate
