import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Tactic

/-!
Candidate: complex-valued convolution on the real line. The starting point is
the earlier generic double-integral formula for the Fourier transform of a
bilinear convolution. The remaining factorization is proved by expanding the
character and factoring the two scalar integrals. The general bilinear/product
convolution identities and Fourier inversion are not invoked. This candidate
still depends on Mathlib's double-integral identity, Fubini, Fourier definitions
and integration infrastructure. External compilation, axiom audit and a
recursive declaration-dependency audit are required.
-/

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace

namespace NativeFourierConvolution

/-- For integrable complex-valued functions on the real line, the Fourier
transform of their convolution is the product of their Fourier transforms. -/
theorem real_complex_convolution_product {f g : ℝ → ℂ}
    (hf : Integrable f) (hg : Integrable g) (ξ : ℝ) :
    FourierTransform.fourier
      (MeasureTheory.convolution f g (ContinuousLinearMap.mul ℂ ℂ) volume) ξ =
        FourierTransform.fourier f ξ * FourierTransform.fourier g ξ := by
  calc
    FourierTransform.fourier
        (MeasureTheory.convolution f g (ContinuousLinearMap.mul ℂ ℂ) volume) ξ =
      ∫ y : ℝ, ∫ x : ℝ,
        Real.fourierChar (-inner ℝ (y + x) ξ) • (f x * g y) :=
          Real.fourier_bilin_convolution_eq_integral
            (ContinuousLinearMap.mul ℂ ℂ) hf hg ξ
    _ = ∫ y : ℝ, ∫ x : ℝ,
        ((Real.fourierChar (-inner ℝ x ξ) : Circle) : ℂ) * f x *
          (((Real.fourierChar (-inner ℝ y ξ) : Circle) : ℂ) * g y) := by
      apply integral_congr_ae
      filter_upwards [] with y
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [inner_add_left, neg_add, AddChar.map_add_eq_mul, Circle.smul_def,
        Circle.coe_mul, smul_eq_mul]
      ring
    _ = (∫ x : ℝ, ((Real.fourierChar (-inner ℝ x ξ) : Circle) : ℂ) * f x) *
          (∫ y : ℝ, ((Real.fourierChar (-inner ℝ y ξ) : Circle) : ℂ) * g y) := by
      simp_rw [integral_mul_const, integral_const_mul]
    _ = FourierTransform.fourier f ξ * FourierTransform.fourier g ξ := by
      rw [Real.fourier_eq, Real.fourier_eq]
      rfl

end NativeFourierConvolution
