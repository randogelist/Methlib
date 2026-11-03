/-
Adapted in part from Mathlib.Analysis.Fourier.RiemannLebesgueLemma,
Copyright (c) 2022 David Loeffler, Apache License 2.0.
This file uses Fourier transform and translation infrastructure, not the
Riemann-Lebesgue theorem itself.
-/
import NativeFourierDecay
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Tactic

noncomputable section

open MeasureTheory Filter Complex Set Module
open scoped Filter Topology Real FourierTransform RealInnerProductSpace

namespace HVRFourierPhase

/-- A half-period shift changes the Fourier integral's sign. -/
theorem half_period_shift (g : ℝ → ℂ) {ξ : ℝ} (hξ : ξ ≠ 0) :
    (∫ t : ℝ, Real.fourierChar (-(t * ξ)) •
      g (t + NativeFourierDecay.halfPeriod ξ)) =
      -NativeFourierDecay.integralTransform g ξ := by
  have hh : NativeFourierDecay.halfPeriod ξ * ξ = (1 / 2 : ℝ) := by
    dsimp [NativeFourierDecay.halfPeriod]
    field_simp [hξ] <;> ring
  have hid :
      (fun t : ℝ => Real.fourierChar (-(t * ξ)) •
        g (t + NativeFourierDecay.halfPeriod ξ)) =
      fun t : ℝ => (fun u : ℝ => -(Real.fourierChar (-(u * ξ)) • g u))
        (t + NativeFourierDecay.halfPeriod ξ) := by
    funext t
    simp_rw [add_mul, hh, Circle.smul_def, Real.fourierChar_apply, neg_add, mul_add,
      ofReal_add, add_mul, exp_add]
    match_scalars
    have H : exp (-(π * I)) = (-1)⁻¹ := by rw [exp_neg, exp_pi_mul_I]
    linear_combination (norm := ring_nf) cexp (-2 * π * (t * ξ) * I) * H
  rw [hid, integral_add_right_eq_self
    (fun u : ℝ => -(Real.fourierChar (-(u * ξ)) • g u))
    (NativeFourierDecay.halfPeriod ξ)]
  simp only [integral_neg, NativeFourierDecay.integralTransform]

/-- The precise half-period cancellation premise of `NativeFourierDecay`. -/
theorem half_period_cancellation (g : ℝ → ℂ) (hg : Integrable g)
    {ξ : ℝ} (hξ : ξ ≠ 0) :
    (2 : ℂ) * NativeFourierDecay.integralTransform g ξ =
      -(∫ t : ℝ, Real.fourierChar (-(t * ξ)) •
        (g (t + NativeFourierDecay.halfPeriod ξ) - g t)) := by
  have hfirst : Integrable (fun t : ℝ => Real.fourierChar (-(t * ξ)) •
      g (t + NativeFourierDecay.halfPeriod ξ)) := by
    simpa only [Real.inner_apply] using
      (Real.fourierIntegral_convergent_iff
        (f := fun t : ℝ => g (t + NativeFourierDecay.halfPeriod ξ)) ξ).2
        (hg.comp_add_right (NativeFourierDecay.halfPeriod ξ))
  have hsecond : Integrable (fun t : ℝ => Real.fourierChar (-(t * ξ)) • g t) := by
    simpa only [Real.inner_apply] using
      (Real.fourierIntegral_convergent_iff (f := g) ξ).2 hg
  have hdifference :
      (∫ t : ℝ, Real.fourierChar (-(t * ξ)) •
        (g (t + NativeFourierDecay.halfPeriod ξ) - g t)) =
      -NativeFourierDecay.integralTransform g ξ -
        NativeFourierDecay.integralTransform g ξ := by
    simp_rw [smul_sub]
    rw [integral_sub hfirst hsecond, half_period_shift g hξ]
    rfl
  rw [hdifference]
  ring

end HVRFourierPhase
