import CondRecurrence

namespace CondFeffA.WJISmooth

open Fefferman Fefferman.ConcreteReal
open scoped ContDiff

noncomputable section

/-- Smooth scalar functions, regarded as actual pointwise representatives. -/
def scalarSpace : Submodule ℝ (RSpace → ℝ) where
  carrier := {f | ContDiff ℝ ∞ f}
  zero_mem' := by
    change ContDiff ℝ ∞ (fun _ : RSpace => (0 : ℝ))
    exact contDiff_const
  add_mem' := by
    intro f g hf hg
    change ContDiff ℝ ∞ f at hf
    change ContDiff ℝ ∞ g at hg
    change ContDiff ℝ ∞ (fun x : RSpace => f x + g x)
    exact hf.add hg
  smul_mem' := by
    intro c f hf
    change ContDiff ℝ ∞ f at hf
    change ContDiff ℝ ∞ (fun x : RSpace => c * f x)
    exact contDiff_const.mul hf

private theorem scalarSmooth (f : scalarSpace) : ContDiff ℝ ∞ f.val := by
  change f.val ∈ scalarSpace
  exact f.property

/-- Componentwise smooth vector fields on the literal whole space. -/
def fieldSpace : Submodule ℝ RInitial where
  carrier := {v | ∀ i : Fin 3, ContDiff ℝ ∞ (fun x : RSpace => v x i)}
  zero_mem' := fun _ => contDiff_const
  add_mem' hv hw := fun i => ContDiff.add (hv i) (hw i)
  smul_mem' _ _ hv := fun i => contDiff_const.mul (hv i)

theorem profile_mem : profile ∈ fieldSpace :=
  fun i => (profile_analytic i).of_le le_top

private def component (i : Fin 3) : fieldSpace →ₗ[ℝ] scalarSpace where
  toFun v := ⟨fun x => v.val x i, v.property i⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- On smooth scalar representatives, the package coordinate derivative is linear. -/
def partialMap (i : Fin 3) : scalarSpace →ₗ[ℝ] scalarSpace where
  toFun f := ⟨spatialDerivative i f.val,
    (contDiff_clm_apply_iff.mp (contDiff_infty_iff_fderiv.mp (scalarSmooth f)).2)
      (basisDirection i)⟩
  map_add' f g := by
    apply Subtype.ext
    funext x
    change (fderiv ℝ (fun y => f.val y + g.val y) x) (basisDirection i) = _
    rw [fderiv_fun_add ((contDiff_infty_iff_fderiv.mp (scalarSmooth f)).1 x)
      ((contDiff_infty_iff_fderiv.mp (scalarSmooth g)).1 x)] <;> rfl
  map_smul' c f := by
    apply Subtype.ext
    funext x
    change (fderiv ℝ (fun y => c * f.val y) x) (basisDirection i) = _
    rw [fderiv_const_mul ((contDiff_infty_iff_fderiv.mp (scalarSmooth f)).1 x) c] <;> rfl

private def scalarLap : scalarSpace →ₗ[ℝ] scalarSpace :=
  (partialMap 0).comp (partialMap 0) + (partialMap 1).comp (partialMap 1) +
    (partialMap 2).comp (partialMap 2)

/-- The literal, componentwise heat operator on smooth fields. -/
def heat : fieldSpace →ₗ[ℝ] fieldSpace where
  toFun v := ⟨heatStep v.val, fun i => (scalarLap (component i v)).property⟩
  map_add' v w := by
    apply Subtype.ext
    funext x i
    exact congrArg (fun f : scalarSpace => f.val x)
      ((scalarLap.comp (component i)).map_add v w)
  map_smul' c v := by
    apply Subtype.ext
    funext x i
    exact congrArg (fun f : scalarSpace => f.val x)
      ((scalarLap.comp (component i)).map_smul c v)

theorem heat_val (v : fieldSpace) : (heat v).val = heatStep v.val := rfl

/-- Pointwise multiplication of smooth scalar representatives. -/
def scalarProduct : scalarSpace →ₗ[ℝ] scalarSpace →ₗ[ℝ] scalarSpace :=
  LinearMap.mk₂ ℝ (fun f g : scalarSpace =>
    (⟨fun x => f.val x * g.val x, by
      change ContDiff ℝ ∞ (fun x : RSpace => f.val x * g.val x)
      exact (scalarSmooth f).mul (scalarSmooth g)⟩ : scalarSpace))
    (fun f g h => by
      apply Subtype.ext
      funext x
      exact add_mul (f.val x) (g.val x) (h.val x))
    (fun c f g => by
      apply Subtype.ext
      funext x
      exact mul_assoc c (f.val x) (g.val x))
    (fun f g h => by
      apply Subtype.ext
      funext x
      exact mul_add (f.val x) (g.val x) (h.val x))
    (fun c f g => by
      apply Subtype.ext
      funext x
      exact mul_left_comm (f.val x) c (g.val x))

theorem partialMap_product (i : Fin 3) (f g : scalarSpace) :
    partialMap i (scalarProduct f g) =
      scalarProduct f (partialMap i g) + scalarProduct g (partialMap i f) := by
  apply Subtype.ext
  funext x
  change (fderiv ℝ (fun y => f.val y * g.val y) x) (basisDirection i) = _
  rw [fderiv_fun_mul ((contDiff_infty_iff_fderiv.mp (scalarSmooth f)).1 x)
    ((contDiff_infty_iff_fderiv.mp (scalarSmooth g)).1 x)] <;> rfl

private def advTerm (j i : Fin 3) :
    fieldSpace →ₗ[ℝ] fieldSpace →ₗ[ℝ] scalarSpace :=
  scalarProduct.compl₁₂ (component j) ((partialMap j).comp (component i))

private def advComponent (i : Fin 3) :
    fieldSpace →ₗ[ℝ] fieldSpace →ₗ[ℝ] scalarSpace :=
  advTerm 0 i + advTerm 1 i + advTerm 2 i

/-- The literal transport before the pressure projection. -/
def advection : fieldSpace →ₗ[ℝ] fieldSpace →ₗ[ℝ] fieldSpace :=
  LinearMap.mk₂ ℝ (fun v w : fieldSpace =>
    (⟨transport v.val w.val, fun i => (advComponent i v w).property⟩ : fieldSpace))
    (fun v z w => by
      apply Subtype.ext
      funext x i
      exact congrArg (fun B : fieldSpace →ₗ[ℝ] scalarSpace => (B w).val x)
        ((advComponent i).map_add v z))
    (fun c v w => by
      apply Subtype.ext
      funext x i
      exact congrArg (fun B : fieldSpace →ₗ[ℝ] scalarSpace => (B w).val x)
        ((advComponent i).map_smul c v))
    (fun v w z => by
      apply Subtype.ext
      funext x i
      exact congrArg (fun f : scalarSpace => f.val x) ((advComponent i v).map_add w z))
    (fun c v w => by
      apply Subtype.ext
      funext x i
      exact congrArg (fun f : scalarSpace => f.val x) ((advComponent i v).map_smul c w))

theorem advection_val (v w : fieldSpace) :
    (advection v w).val = transport v.val w.val := rfl

/-- Restrict the concrete heat operator to any invariant smooth subspace. -/
def heatOn (S : Submodule ℝ RInitial) (hS : S ≤ fieldSpace)
    (hclosed : ∀ v : S, heatStep v.val ∈ S) : S →ₗ[ℝ] S where
  toFun v := ⟨heatStep v.val, hclosed v⟩
  map_add' v w := by
    apply Subtype.ext
    exact congrArg (fun z : fieldSpace => z.val)
      (heat.map_add ⟨v.val, hS v.property⟩ ⟨w.val, hS w.property⟩)
  map_smul' c v := by
    apply Subtype.ext
    exact congrArg (fun z : fieldSpace => z.val) (heat.map_smul c ⟨v.val, hS v.property⟩)

/-- Restrict the concrete transport to any invariant smooth subspace. -/
def advectionOn (S : Submodule ℝ RInitial) (hS : S ≤ fieldSpace)
    (hclosed : ∀ v w : S, transport v.val w.val ∈ S) : S →ₗ[ℝ] S →ₗ[ℝ] S :=
  LinearMap.mk₂ ℝ (fun v w : S => (⟨transport v.val w.val, hclosed v w⟩ : S))
    (fun v z w => by
      apply Subtype.ext
      exact congrArg (fun B : fieldSpace →ₗ[ℝ] fieldSpace => (B ⟨w.val, hS w.property⟩).val)
        (advection.map_add ⟨v.val, hS v.property⟩ ⟨z.val, hS z.property⟩))
    (fun c v w => by
      apply Subtype.ext
      exact congrArg (fun B : fieldSpace →ₗ[ℝ] fieldSpace => (B ⟨w.val, hS w.property⟩).val)
        (advection.map_smul c ⟨v.val, hS v.property⟩))
    (fun v w z => by
      apply Subtype.ext
      exact congrArg (fun a : fieldSpace => a.val)
        ((advection ⟨v.val, hS v.property⟩).map_add ⟨w.val, hS w.property⟩ ⟨z.val, hS z.property⟩))
    (fun c v w => by
      apply Subtype.ext
      exact congrArg (fun a : fieldSpace => a.val)
        ((advection ⟨v.val, hS v.property⟩).map_smul c ⟨w.val, hS w.property⟩))

end
end CondFeffA.WJISmooth
