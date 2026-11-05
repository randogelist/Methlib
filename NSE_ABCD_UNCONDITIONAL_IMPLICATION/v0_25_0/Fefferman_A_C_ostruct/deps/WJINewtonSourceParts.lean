import WJINewtonWeakGradient
import WJIGradientL2

namespace CondFeffA
open Fefferman Fefferman.ConcreteReal MeasureTheory Set Filter
open scoped ContDiff BigOperators
noncomputable section

local notation "D" => spatialDerivative

private lemma flip_integrable {f g : RSpace → ℝ} {x : RSpace}
    (h : Integrable (fun y => f y * g (x-y))) :
    Integrable (fun y : RSpace => g y * f (x-y)) := by
  simpa only [sub_sub_self, mul_comm] using h.comp_sub_left x

/-- No support restriction on the source. The integrability and pointwise
bounds on one derivative and the source provide the three dominating products. -/
theorem wji_newtonPotential_partial_source_parts (i : Fin 3) {f : RSpace → ℝ}
    (hs : ContDiff ℝ ∞ f) (hf : Integrable f) (hd : Integrable (D i f))
    {A B : ℝ} (hA : ∀ y, ‖f y‖ ≤ A) (hB : ∀ y, ‖D i f y‖ ≤ B) (x : RSpace) :
    newtonPotential (D i f) x = ∫ y, f y * newtonGradientKernel i (x-y) := by
  let e : RSpace → RSpace := fun y => x-y
  let T := f ∘ e
  have hT : ContDiff ℝ ∞ T := hs.comp (contDiff_const.sub contDiff_id)
  have he (y : RSpace) : HasFDerivAt e (-(ContinuousLinearMap.id ℝ RSpace)) y := by
    change HasFDerivAt (fun z : RSpace => x - z) (-(ContinuousLinearMap.id ℝ RSpace)) y
    exact (hasFDerivAt_id (𝕜 := ℝ) y).const_sub x
  have ht (y : RSpace) : D i T y = -D i f (x-y) := by
    have h := ((contDiff_infty_iff_fderiv.mp hs).1 (e y)).hasFDerivAt.comp y (he y)
    calc
      (fderiv ℝ (f ∘ e) y) (basisDirection i) =
          (fderiv ℝ f (e y)) ((-(ContinuousLinearMap.id ℝ RSpace)) (basisDirection i)) :=
        congrArg (fun L : RSpace →L[ℝ] ℝ => L (basisDirection i)) h.fderiv
      _ = -D i f (x-y) := by
        change (fderiv ℝ f (x-y)) (-(basisDirection i)) = _
        rw [map_neg] <;> rfl
  have hv := flip_integrable (integrable_newton_majorized (k := 1) (by decide)
    newtonKernel_measurable newtonKernel_majorized hf hA x)
  have hD := flip_integrable (integrable_newton_majorized (k := 1) (by decide)
    newtonKernel_measurable newtonKernel_majorized hd hB x)
  have hG := flip_integrable (newtonGradientIntegrand_integrable hf hA i x)
  have negFun : (fun y => newtonKernel y * D i T y) =
      fun y => -(newtonKernel y * D i f (x-y)) := by
    funext y
    rw [ht, mul_neg]
  have hdT : Integrable (fun y => newtonKernel y * D i T y) := by
    rw [negFun]
    exact hD.neg
  have hi := wji_newtonKernel_weak_gradient_of_integrable i hT hv hdT hG
  rw [negFun, integral_neg] at hi
  calc
    newtonPotential (D i f) x = ∫ y, D i f y * newtonKernel (x-y) := by
      simp only [newtonPotential, newtonKernel, div_eq_mul_inv]
    _ = ∫ y, newtonKernel y * D i f (x-y) := wji_convolution_swap _ _ _
    _ = ∫ y, newtonGradientKernel i y * f (x-y) := neg_injective hi
    _ = _ := (wji_convolution_swap _ _ _).symm

private lemma transport_coord_deriv_L1 (v w : WJISobolev.space) (i j : Fin 3) :
    Integrable (D i (fun x => transport v.val w.val x j)) := by
  let comp (u : WJISobolev.space) (a : Fin 3) : WJISmooth.scalarSpace :=
    ⟨fun y => u.val y a, WJISobolev.scalar_smooth (u.property a)⟩
  let term (a : Fin 3) :=
    WJISmooth.scalarProduct (comp v a) (WJISmooth.partialMap a (comp w j))
  have hterm (a : Fin 3) : Integrable (WJISmooth.partialMap i (term a)).val := by
    change Integrable (WJISmooth.partialMap i (WJISmooth.scalarProduct (comp v a)
      (WJISmooth.partialMap a (comp w j)))).val
    rw [WJISmooth.partialMap_product]
    have h₂ := (WJISobolev.scalar_memLp
      (WJISobolev.scalar_partial (WJISobolev.scalar_partial (w.property j) a) i)).1
    exact (memLp_one_iff_integrable.mp (h₂.mul' (WJISobolev.memLp_coord v a))).add
      (memLp_one_iff_integrable.mp ((WJISobolev.memLp_partial v a i).mul'
        (WJISobolev.memLp_partial w j a)))
  change Integrable (WJISmooth.partialMap i (term 0 + term 1 + term 2)).val
  rw [map_add, map_add]
  exact ((hterm 0).add (hterm 1)).add (hterm 2)

/-- The Newton scalar of a transport divergence has the explicit integral
obtained by moving each spatial derivative from the source onto the kernel. -/
theorem wji_newton_transport_parts (v w : WJISobolev.space) (x : RSpace) :
    newtonPotential (fieldDiv (transport v.val w.val)) x =
      ∑ j : Fin 3, ∫ y, transport v.val w.val y j * newtonGradientKernel j (x-y) := by
  let F := transport v.val w.val
  let d (j : Fin 3) := D j (fun y => F y j)
  have hF := WJISobolev.transport_mem v w
  have hpart (j : Fin 3) : newtonPotential (d j) x =
      ∫ y, F y j * newtonGradientKernel j (x-y) := by
    obtain ⟨A, hA⟩ := WJISobolev.scalar_bounded (hF j)
    obtain ⟨B, hB⟩ := WJISobolev.scalar_bounded (WJISobolev.scalar_partial (hF j) j)
    exact wji_newtonPotential_partial_source_parts j (WJISobolev.scalar_smooth (hF j))
      (wji_transport_component_integrable v w j) (transport_coord_deriv_L1 v w j j) hA hB x
  have hi (j : Fin 3) : Integrable
      (fun y => d j y / (4*Real.pi * euclideanNorm3 (x-y))) := by
    obtain ⟨B, hB⟩ := WJISobolev.scalar_bounded (WJISobolev.scalar_partial (hF j) j)
    exact newtonIntegrand_integrable (transport_coord_deriv_L1 v w j j) hB x
  calc
    newtonPotential (fieldDiv F) x =
        (newtonPotential (d 0) x + newtonPotential (d 1) x) + newtonPotential (d 2) x := by
      let q (j : Fin 3) (y : RSpace) := d j y / (4 * Real.pi * euclideanNorm3 (x-y))
      have hq (j : Fin 3) : Integrable (q j) := hi j
      change (∫ y, ((d 0 y + d 1 y) + d 2 y) / (4 * Real.pi * euclideanNorm3 (x-y))) = _
      simp only [add_div, newtonPotential]
      change (∫ y, (q 0 y + q 1 y) + q 2 y) =
        ((∫ y, q 0 y) + (∫ y, q 1 y)) + (∫ y, q 2 y)
      calc
        _ = (∫ y, q 0 y + q 1 y) + (∫ y, q 2 y) :=
          integral_add (f := fun y => q 0 y + q 1 y) (g := q 2) ((hq 0).add (hq 1)) (hq 2)
        _ = _ := congrArg (fun t : ℝ => t + (∫ y, q 2 y)) (integral_add (hq 0) (hq 1))
    _ = _ := by rw [hpart 0, hpart 1, hpart 2, Fin.sum_univ_three] <;> abel

/-- The literal Newton potential of a transport divergence lies in L². -/
theorem wji_newton_transport_potential_memL2 (v w : WJISobolev.space) :
    MemLp (newtonPotential (fieldDiv (transport v.val w.val))) 2 volume :=
  wji_newtonPotential_memL2_of_parts v w (wji_newton_transport_parts v w)

end
end CondFeffA
