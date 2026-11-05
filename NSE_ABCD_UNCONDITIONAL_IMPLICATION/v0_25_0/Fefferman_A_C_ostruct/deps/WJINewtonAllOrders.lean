import WJINewtonSourceWords
import WJINewtonTranslate
import WJISmoothCommutation

namespace CondFeffA
open Fefferman Fefferman.ConcreteReal WJISmooth MeasureTheory
open scoped ContDiff
noncomputable section

local notation "D" => spatialDerivative
local notation "N" => newtonPotential

/-- Every coordinate derivative is in L¹, and all of them also have the bounded
continuous representatives supplied by the concrete Sobolev submodule. -/
private def sourceClass (g : RSpace → ℝ) : Prop :=
  g ∈ WJISobolev.scalar ∧ ∀ w : List (Fin 3), Integrable (wjiSpatialWord w g)

private theorem source_partial {g : RSpace → ℝ} (hg : sourceClass g) (i : Fin 3) :
    sourceClass (D i g) :=
  ⟨WJISobolev.scalar_partial hg.1 i, fun w => hg.2 (i :: w)⟩

private theorem source_word {g : RSpace → ℝ} (hg : sourceClass g) (w : List (Fin 3)) :
    sourceClass (wjiSpatialWord w g) := by
  induction w generalizing g with
  | nil => exact hg
  | cons i w ih => exact ih (source_partial hg i)

private theorem transport_source_class (v u : WJISobolev.space) :
    sourceClass (fieldDiv (transport v.val u.val)) := by
  have ht := WJISobolev.transport_mem v u
  have hd (i : Fin 3) := WJISobolev.scalar_partial (ht i) i
  exact ⟨WJISobolev.scalar.add_mem (WJISobolev.scalar.add_mem (hd 0) (hd 1)) (hd 2),
    fun w => (wji_transport_source_word v u w).1⟩

private theorem partial_N {g : RSpace → ℝ} (hg : sourceClass g) (i : Fin 3) :
    D i (N g) = N (D i g) := by
  have hd := source_partial hg i
  obtain ⟨A, hA⟩ := WJISobolev.scalar_bounded hg.1
  obtain ⟨B, hB⟩ := WJISobolev.scalar_bounded hd.1
  exact funext (wji_partial_newton_eq_newton_partial i (WJISobolev.scalar_smooth hg.1)
    (hg.2 []) (hd.2 []) hA hB)

private theorem frechet_coord_sum (f : RSpace → ℝ) (x y : RSpace) :
    fderiv ℝ f x y = y 0 * D 0 f x + y 1 * D 1 f x + y 2 * D 2 f x := by
  have hv : y = y 0 • basisDirection 0 + y 1 • basisDirection 1 + y 2 • basisDirection 2 := by
    funext i
    fin_cases i
    · change y 0 = y 0 * 1 + y 1 * 0 + y 2 * 0
      ring
    · change y 1 = y 0 * 0 + y 1 * 1 + y 2 * 0
      ring
    · change y 2 = y 0 * 0 + y 1 * 0 + y 2 * 1
      ring
  calc
    _ = fderiv ℝ f x (y 0 • basisDirection 0 + y 1 • basisDirection 1 + y 2 • basisDirection 2) :=
      congrArg (fun z : RSpace => fderiv ℝ f x z) hv
    _ = _ := by simp only [map_add, map_smul, smul_eq_mul, spatialDerivative]

private theorem N_smooth {g : RSpace → ℝ} (hg : sourceClass g) : ContDiff ℝ ∞ (N g) := by
  apply contDiff_infty.mpr
  intro m
  induction m generalizing g with
  | zero =>
    obtain ⟨M, hM⟩ := WJISobolev.scalar_bounded hg.1
    exact contDiff_zero.mpr
      (newtonPotential_differentiable_of_smooth_bounded_L1
        (WJISobolev.scalar_smooth hg.1) (hg.2 []) hM).continuous
  | succ m ih =>
    rw [Nat.cast_succ, contDiff_succ_iff_fderiv_apply]
    obtain ⟨M, hM⟩ := WJISobolev.scalar_bounded hg.1
    refine ⟨newtonPotential_differentiable_of_smooth_bounded_L1
      (WJISobolev.scalar_smooth hg.1) (hg.2 []) hM, ?_, ?_⟩
    · intro h
      exact False.elim ((WithTop.coe_ne_top : ((m : ℕ∞) : ℕ∞ω) ≠ ⊤) h)
    · intro y
      have he : (fun x => fderiv ℝ (N g) x y) = fun x =>
          y 0 * N (D 0 g) x + y 1 * N (D 1 g) x + y 2 * N (D 2 g) x := by
        funext x
        rw [frechet_coord_sum, partial_N hg 0, partial_N hg 1, partial_N hg 2]
      rw [he]
      exact (((contDiff_const.mul (ih (source_partial hg 0))).add
        (contDiff_const.mul (ih (source_partial hg 1)))).add
        (contDiff_const.mul (ih (source_partial hg 2))))

theorem wji_newton_scalar_smooth (v u : WJISobolev.space) :
    ContDiff ℝ ∞ (wjiNewtonScalar v.val u.val) := N_smooth (transport_source_class v u)

private theorem word_N {g : RSpace → ℝ} (hg : sourceClass g) (w : List (Fin 3)) :
    wjiSpatialWord w (N g) = N (wjiSpatialWord w g) := by
  induction w generalizing g with
  | nil => rfl
  | cons i w ih =>
    change wjiSpatialWord w (D i (N g)) = N (wjiSpatialWord w (D i g))
    rw [partial_N hg i]
    exact ih (source_partial hg i)

private theorem word_partial {f : RSpace → ℝ} (hf : ContDiff ℝ ∞ f)
    (i : Fin 3) (w : List (Fin 3)) :
    wjiSpatialWord w (D i f) = D i (wjiSpatialWord w f) := by
  induction w generalizing f with
  | nil => rfl
  | cons j w ih =>
    change wjiSpatialWord w (D j (D i f)) = D i (wjiSpatialWord w (D j f))
    rw [wji_smooth_partial_comm hf j i]
    exact ih ((partialMap j ⟨f,hf⟩).property)

/-- The derivative word on the potential gradient transfers onto the transport
source. A single gradient remains on the Newton kernel. -/
theorem wji_newton_word_gradient_formula (v u : WJISobolev.space)
    (i : Fin 3) (w : List (Fin 3)) :
    wjiSpatialWord w (D i (wjiNewtonScalar v.val u.val)) =
      fun x => ∫ y, wjiSpatialWord w (fieldDiv (transport v.val u.val)) y *
        newtonGradientKernel i (x-y) := by
  let g := fieldDiv (transport v.val u.val)
  have hg : sourceClass g := transport_source_class v u
  have hw := source_word hg w
  obtain ⟨A, hA⟩ := WJISobolev.scalar_bounded hw.1
  calc
    wjiSpatialWord w (D i (N g)) = D i (wjiSpatialWord w (N g)) :=
      word_partial (N_smooth hg) i w
    _ = D i (N (wjiSpatialWord w g)) := congrArg (D i) (word_N hg w)
    _ = _ := funext (wji_partial_newton_eq_kernel_of_smooth i (WJISobolev.scalar_smooth hw.1)
      (hw.2 []) hA)

theorem wji_newton_gradient_regular (v u : WJISobolev.space) :
    wjiScalarGradient (wjiNewtonScalar v.val u.val) ∈ WJISobolev.space :=
  wji_gradient_mem_of_kernel_words v u
    (fun i => (partialMap i ⟨_, wji_newton_scalar_smooth v u⟩).property)
    (wji_newton_word_gradient_formula v u)

end
end CondFeffA
