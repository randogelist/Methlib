import WJIWordTrace
import WJIGradientL2
import WJINewtonPoisson

namespace CondFeffA
open Fefferman Fefferman.ConcreteReal WJISmooth MeasureTheory Filter
open scoped ContDiff
noncomputable section

/-- Realize a coordinate word as a linear map of smooth representatives. -/
private def wordMap : List (Fin 3) → scalarSpace →ₗ[ℝ] scalarSpace
  | [] => LinearMap.id
  | i :: w => (wordMap w).comp (partialMap i)

private theorem wordMap_val (w : List (Fin 3)) (f : scalarSpace) :
    (wordMap w f).val = wjiSpatialWord w f.val := by
  induction w generalizing f with
  | nil => rfl
  | cons i w ih => exact ih (partialMap i f)

private theorem word_mem_scalar (w : List (Fin 3)) {f : RSpace → ℝ}
    (hf : f ∈ WJISobolev.scalar) : wjiSpatialWord w f ∈ WJISobolev.scalar := by
  induction w generalizing f with
  | nil => exact hf
  | cons i w ih => exact ih (WJISobolev.scalar_partial hf i)

/-- Differentiating an L² product by any coordinate word gives a finite sum of
L² × L² products. Only the factors need have Sobolev-controlled derivatives. -/
private theorem product_word_integrable (w : List (Fin 3)) (f g : scalarSpace)
    (hf : f.val ∈ WJISobolev.scalar) (hg : g.val ∈ WJISobolev.scalar) :
    Integrable (wordMap w (scalarProduct f g)).val := by
  induction w generalizing f g with
  | nil =>
    exact memLp_one_iff_integrable.mp ((WJISobolev.scalar_memLp hg).1.mul'
      (WJISobolev.scalar_memLp hf).1)
  | cons i w ih =>
    change Integrable (wordMap w (partialMap i (scalarProduct f g))).val
    rw [partialMap_product, map_add]
    exact (ih f (partialMap i g) hf (WJISobolev.scalar_partial hg i)).add
      (ih g (partialMap i f) hg (WJISobolev.scalar_partial hf i))

private theorem source_word_integrable (v u : WJISobolev.space) (w : List (Fin 3)) :
    Integrable (wjiSpatialWord w (fieldDiv (transport v.val u.val))) := by
  let C (z : WJISobolev.space) (j : Fin 3) : scalarSpace :=
    ⟨fun x => z.val x j, WJISobolev.scalar_smooth (z.property j)⟩
  let term (i j : Fin 3) := scalarProduct (C v j) (partialMap j (C u i))
  let diag (i : Fin 3) := partialMap i (term i 0 + term i 1 + term i 2)
  have ht (i j : Fin 3) : Integrable (wordMap (i :: w) (term i j)).val :=
    product_word_integrable (i :: w) (C v j) (partialMap j (C u i))
      (v.property j) (WJISobolev.scalar_partial (u.property i) j)
  have hd (i : Fin 3) : Integrable (wordMap w (diag i)).val := by
    change Integrable (wordMap (i :: w) (term i 0 + term i 1 + term i 2)).val
    rw [map_add, map_add]
    exact ((ht i 0).add (ht i 1)).add (ht i 2)
  have hsource : fieldDiv (transport v.val u.val) = (diag 0 + diag 1 + diag 2).val := by
    funext x
    rfl
  have he : wjiSpatialWord w (fieldDiv (transport v.val u.val)) =
      (wordMap w (diag 0 + diag 1 + diag 2)).val :=
    (congrArg (wjiSpatialWord w) hsource).trans (wordMap_val w (diag 0 + diag 1 + diag 2)).symm
  rw [he, map_add, map_add]
  exact ((hd 0).add (hd 1)).add (hd 2)

private theorem source_mem_scalar (v u : WJISobolev.space) :
    fieldDiv (transport v.val u.val) ∈ WJISobolev.scalar := by
  have ht := WJISobolev.transport_mem v u
  have hd (i : Fin 3) := WJISobolev.scalar_partial (ht i) i
  exact WJISobolev.scalar.add_mem (WJISobolev.scalar.add_mem (hd 0) (hd 1)) (hd 2)

/-- Every derivative of the actual Newton source is simultaneously integrable,
square integrable and pointwise bounded. -/
theorem wji_transport_source_word (v u : WJISobolev.space) (w : List (Fin 3)) :
    let g := wjiSpatialWord w (fieldDiv (transport v.val u.val))
    Integrable g ∧ MemLp g 2 volume ∧ ∃ M : ℝ, ∀ x, ‖g x‖ ≤ M :=
  let h := word_mem_scalar w (source_mem_scalar v u)
  ⟨source_word_integrable v u w, (WJISobolev.scalar_memLp h).1, WJISobolev.scalar_bounded h⟩

/-- The differentiated Newton formula implies Sobolev closure of the gradient;
integrability, measurability, and kernel estimates are discharged on every word. -/
theorem wji_gradient_mem_of_kernel_words (v u : WJISobolev.space)
    (hsmooth : ∀ i : Fin 3, ContDiff ℝ ∞ (spatialDerivative i (wjiNewtonScalar v.val u.val)))
    (hwords : ∀ (i : Fin 3) (w : List (Fin 3)),
      wjiSpatialWord w (spatialDerivative i (wjiNewtonScalar v.val u.val)) =
        fun x => ∫ y, wjiSpatialWord w (fieldDiv (transport v.val u.val)) y *
          newtonGradientKernel i (x-y)) :
    wjiScalarGradient (wjiNewtonScalar v.val u.val) ∈ WJISobolev.space := by
  intro i
  change spatialDerivative i (wjiNewtonScalar v.val u.val) ∈ WJISobolev.scalar
  apply wji_scalar_sobolev_of_word_bounds (hsmooth i)
  intro w
  rw [hwords i w]
  let g := wjiSpatialWord w (fieldDiv (transport v.val u.val))
  have hs := word_mem_scalar w (source_mem_scalar v u)
  obtain ⟨h1, h2, M, hM⟩ := wji_transport_source_word v u w
  have hL : MemLp (fun x => ∫ y, g y * newtonGradientKernel i (x-y)) 2 volume :=
    wji_newtonGradient_convolution_memL2 i h1 h2
      (WJISobolev.scalar_smooth hs).continuous.measurable hM
  refine ⟨hL, memLp_top_of_bound hL.aestronglyMeasurable
    (M * newtonLocalMass 2 + ∫ y, ‖g y‖) ?_⟩
  exact Filter.Eventually.of_forall (newtonGradientIntegral_norm_le h1 hM i)

end
end CondFeffA
