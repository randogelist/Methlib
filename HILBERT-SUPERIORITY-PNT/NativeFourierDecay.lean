import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Tactic

/-!
Conditional translation route to Fourier decay on the real line.

This helper leaves two explicit obligations: the half-period translation
identity, and convergence to zero of the L1 translation difference along the
half-period shifts. Neither obligation is asserted for an arbitrary integrable
function by this file. The proof uses the elementary norm bound for a Bochner
integral and a norm squeeze. No Riemann--Lebesgue theorem is cited. Matching
external compilation, axiom audit and recursive dependency audit are required.
-/

noncomputable section

open Filter MeasureTheory
open scoped Topology

namespace NativeFourierDecay

/-- The usual Fourier integral on the real line, in the 2π convention. -/
def integralTransform (g : ℝ → ℂ) (ξ : ℝ) : ℂ :=
  ∫ t : ℝ, Real.fourierChar (-(t * ξ)) • g t

/-- A shift of this size changes the character by a half-period when ξ ≠ 0. -/
def halfPeriod (ξ : ℝ) : ℝ := (2 * ξ)⁻¹

/-- The L1 size of the corresponding translate difference. -/
def translationDifference (g : ℝ → ℂ) (ξ : ℝ) : ℝ :=
  ∫ t : ℝ, ‖g (t + halfPeriod ξ) - g t‖

/-- Fourier decay follows from a half-period cancellation identity and
vanishing L1 translation differences along the frequency parameter. -/
theorem decay_from_half_period_obligations (g : ℝ → ℂ)
    (hphase : ∀ᶠ ξ : ℝ in atTop,
      (2 : ℂ) * integralTransform g ξ =
        -(∫ t : ℝ, Real.fourierChar (-(t * ξ)) •
          (g (t + halfPeriod ξ) - g t)))
    (htranslation : Tendsto (translationDifference g) atTop (𝓝 0)) :
    Tendsto (integralTransform g) atTop (𝓝 0) := by
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

end NativeFourierDecay
