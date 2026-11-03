import Mathlib.Analysis.Fourier.FourierTransform

/-!
# Native Fourier inverse sign identity

This candidate proves the exact general real-inner-product-space statement of
the standard inverse/forward sign lemma by comparing the two defining Fourier integral
formulas. No integrability hypothesis is introduced. It does not establish a
Fourier inversion theorem. The proof retains Mathlib's Fourier definitions and
integral formulas; its own compiler, axiom and declaration-dependency audits
are required before claiming verification or target independence.
-/

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace

namespace NativeFourierInverse

variable {V E : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]
variable [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The inverse Fourier transform at `w` is the forward transform at `-w`.
This follows from the integral conventions and uses no Fourier inversion. -/
theorem inverse_as_forward_at_negative (f : V → E) (w : V) :
    FourierTransformInv.fourierInv f w = FourierTransform.fourier f (-w) := by
  rw [Real.fourierInv_eq, Real.fourier_eq]
  apply integral_congr_ae
  filter_upwards [] with v
  simp only [inner_neg_right, neg_neg]

end NativeFourierInverse
