import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
Candidate full coordinate-series formula for the inner product on an ℓ²
Hilbert sum. Mathlib's Hilbert-sum inner-product instance itself is defined by
this series, so the identity is definitional. This is not an independent
construction of the Hilbert space or its inner product. External compilation,
axiom auditing and declaration-dependency inspection are still required.
-/

noncomputable section

namespace NativeLpInner

variable {ι 𝕜 : Type*} [RCLike 𝕜]
variable {G : ι → Type*}
variable [∀ i, NormedAddCommGroup (G i)]
variable [∀ i, InnerProductSpace 𝕜 (G i)]

/-- The Hilbert-sum inner product equals the coordinate inner-product series. -/
theorem lp_inner_as_coordinate_series (f g : lp G 2) :
    inner 𝕜 f g = ∑' i, inner 𝕜 (f i) (g i) := by
  rfl

end NativeLpInner
