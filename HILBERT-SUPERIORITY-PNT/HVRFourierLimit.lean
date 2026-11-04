import NativeFourierDecay
import Mathlib.Tactic

/-!
Filter-generic limit transfer for the half-period translation argument.
The endpoint is conditional: a proof of the translation identity and an L1
translation limit must be supplied. The old file covers only `atTop`; this
form also applies to `atBot` and to the cocompact filter on the real line.
No claim of transitive Mathlib dependency independence is made.
-/

noncomputable section
open Filter MeasureTheory NativeFourierDecay
open scoped Topology

namespace HVRFourierLimit

/-- The Fourier-decay norm squeeze holds for any frequency filter. -/
theorem decay_of_half_period_obligations (g : ℝ → ℂ) (l : Filter ℝ)
    (hphase : ∀ᶠ ξ : ℝ in l,
      (2 : ℂ) * integralTransform g ξ =
        -(∫ t : ℝ, Real.fourierChar (-(t * ξ)) •
          (g (t + halfPeriod ξ) - g t)))
    (htranslation : Tendsto (translationDifference g) l (𝓝 0)) :
    Tendsto (integralTransform g) l (𝓝 0) := by
  apply squeeze_zero_norm' ?_ htranslation
  filter_upwards [hphase] with ξ hξ
  have hi :
      ‖∫ t : ℝ, Real.fourierChar (-(t * ξ)) •
          (g (t + halfPeriod ξ) - g t) ∂volume‖ ≤
        ∫ t : ℝ, ‖Real.fourierChar (-(t * ξ)) •
          (g (t + halfPeriod ξ) - g t)‖ ∂volume :=
    norm_integral_le_integral_norm _
  have hid : (2 : ℝ) * ‖integralTransform g ξ‖ =
      ‖∫ t : ℝ, Real.fourierChar (-(t * ξ)) •
        (g (t + halfPeriod ξ) - g t)‖ := by
    calc
      _ = ‖(2 : ℂ) * integralTransform g ξ‖ := by simp
      _ = ‖-(∫ t : ℝ, Real.fourierChar (-(t * ξ)) •
          (g (t + halfPeriod ξ) - g t))‖ := by rw [hξ]
      _ = _ := norm_neg _
  have hnorm : (2 : ℝ) * ‖integralTransform g ξ‖ ≤
      translationDifference g ξ := by
    rw [hid]
    simpa only [translationDifference, Circle.norm_smul] using hi
  have hnonneg : 0 ≤ ‖integralTransform g ξ‖ := norm_nonneg _
  nlinarith

end HVRFourierLimit
