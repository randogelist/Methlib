import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Tactic

noncomputable section
open MeasureTheory

/-!
A concrete normalized, nonnegative and even smooth frequency seed at an
arbitrary positive bandwidth. This is a compactly supported frequency-space
bump, not yet the nonnegative band-limited physical smoothing kernel. Inverse
Fourier transform, squaring, spectral support of the square, and physical-side
normalization remain open. No Lean execution was performed locally.
-/
namespace HVRSmoothingFrequencySeed

/-- A symmetric bump with outer radius half the requested bandwidth. -/
def bump (w : ℝ) (hw : 0 < w) : ContDiffBump (0 : ℝ) where
  rIn := w / 4
  rOut := w / 2
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith

/-- Its Lebesgue-integral normalization, used as a Fourier-space seed. -/
def seed (w : ℝ) (hw : 0 < w) : ℝ → ℝ :=
  (bump w hw).normed volume

theorem seed_nonneg (w : ℝ) (hw : 0 < w) (x : ℝ) :
    0 ≤ seed w hw x :=
  (bump w hw).nonneg_normed x

theorem seed_even (w : ℝ) (hw : 0 < w) (x : ℝ) :
    seed w hw (-x) = seed w hw x :=
  (bump w hw).normed_neg x

/-- The seed is C-infinity. The outer top of WithTop ℕ∞ would instead
assert analyticity, which a nonzero compactly supported bump cannot have. -/
theorem seed_smooth_Cinfty (w : ℝ) (hw : 0 < w) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (seed w hw) := by
  simpa only [seed] using
    ((bump w hw).contDiff_normed (μ := volume) (n := ⊤))

theorem seed_compact (w : ℝ) (hw : 0 < w) :
    HasCompactSupport (seed w hw) :=
  (bump w hw).hasCompactSupport_normed

theorem seed_integrable (w : ℝ) (hw : 0 < w) :
    Integrable (seed w hw) volume :=
  (bump w hw).integrable_normed

theorem seed_integral (w : ℝ) (hw : 0 < w) :
    (∫ x : ℝ, seed w hw x) = 1 :=
  (bump w hw).integral_normed

theorem seed_support (w : ℝ) (hw : 0 < w) :
    Function.support (seed w hw) = Metric.ball (0 : ℝ) (w / 2) := by
  exact (bump w hw).support_normed_eq

theorem seed_zero_of_band (w : ℝ) (hw : 0 < w) (x : ℝ)
    (hx : w / 2 ≤ |x|) : seed w hw x = 0 := by
  have hdist : (bump w hw).rOut ≤ dist x (0 : ℝ) := by
    simpa only [bump, Real.dist_eq, sub_zero] using hx
  unfold seed
  rw [ContDiffBump.normed_def, (bump w hw).zero_of_le_dist hdist, zero_div]

end HVRSmoothingFrequencySeed
