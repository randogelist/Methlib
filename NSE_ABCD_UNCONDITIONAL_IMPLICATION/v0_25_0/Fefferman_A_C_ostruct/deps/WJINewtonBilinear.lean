import WJINewtonSmooth
import WJIFieldRows

namespace CondFeffA

open Fefferman Fefferman.ConcreteReal MeasureTheory
noncomputable section

private abbrev Sob := WJISobolev.space
private abbrev ScalarField := RSpace → ℝ

private def integralSource : Submodule ℝ ScalarField where
  carrier := {g | ∀ x : RSpace, Integrable (fun y : RSpace =>
    g y / (4 * Real.pi * euclideanNorm3 (x-y)))}
  zero_mem' := by intro x; simp
  add_mem' := by
    intro f g hf hg x
    change Integrable (fun y : RSpace => (f y + g y) / (4 * Real.pi * euclideanNorm3 (x-y)))
    simp only [add_div]
    exact (hf x).fun_add (hg x)
  smul_mem' c g hg x := by
    simpa only [Pi.smul_apply, smul_eq_mul, mul_div_assoc] using (hg x).const_mul c

/-- Linearity holds on sources whose defining Newton integrals exist at every point. -/
private def potentialMap : integralSource →ₗ[ℝ] ScalarField where
  toFun g := newtonPotential g.val
  map_add' f g := by
    funext x
    change (∫ y, (f.val y + g.val y) / (4 * Real.pi * euclideanNorm3 (x-y))) =
      newtonPotential f.val x + newtonPotential g.val x
    simp only [add_div]
    exact integral_add (f.property x) (g.property x)
  map_smul' c f := by
    funext x
    change (∫ y, (c * f.val y) / (4 * Real.pi * euclideanNorm3 (x-y))) =
      c * newtonPotential f.val x
    simp only [mul_div_assoc]
    exact integral_const_mul c (fun y => f.val y / (4 * Real.pi * euclideanNorm3 (x-y)))

private def restrictBilinear {E F G : Type*} [AddCommGroup E] [AddCommGroup F] [AddCommGroup G]
    [Module ℝ E] [Module ℝ F] [Module ℝ G] (B : E →ₗ[ℝ] F →ₗ[ℝ] G)
    (S : Submodule ℝ G) (h : ∀ v w, B v w ∈ S) : E →ₗ[ℝ] F →ₗ[ℝ] S :=
  LinearMap.mk₂ ℝ (fun v w => (⟨B v w, h v w⟩ : S))
    (fun v z w => by
      apply Subtype.ext
      exact congrArg (fun A : F →ₗ[ℝ] G => A w) (B.map_add v z))
    (fun c v w => by
      apply Subtype.ext
      exact congrArg (fun A : F →ₗ[ℝ] G => A w) (B.map_smul c v))
    (fun v w z => by
      apply Subtype.ext
      exact (B v).map_add w z)
    (fun c v w => by
      apply Subtype.ext
      exact (B v).map_smul c w)

private def sobCoord (i : Fin 3) : Sob →ₗ[ℝ] WJISmooth.scalarSpace where
  toFun v := ⟨fun x => v.val x i, WJISobolev.scalar_smooth (v.property i)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def sobDiv : Sob →ₗ[ℝ] ScalarField :=
  WJISmooth.scalarSpace.subtype.comp
    ((WJISmooth.partialMap 0).comp (sobCoord 0) + (WJISmooth.partialMap 1).comp (sobCoord 1) +
      (WJISmooth.partialMap 2).comp (sobCoord 2))

private def sobAdv : Sob →ₗ[ℝ] Sob →ₗ[ℝ] Sob :=
  WJISmooth.advectionOn Sob WJISobolev.space_smooth WJISobolev.transport_mem

private def newtonSourceBilinear : Sob →ₗ[ℝ] Sob →ₗ[ℝ] integralSource :=
  restrictBilinear (sobAdv.compr₂ sobDiv) integralSource
    (fun v w x => (wji_newton_transport_integrands v w x).1)

/-- The scalar Newton potential itself is bilinear on the transport pair. -/
def wjiNewtonScalarBilinear : Sob →ₗ[ℝ] Sob →ₗ[ℝ] ScalarField :=
  newtonSourceBilinear.compr₂ potentialMap

theorem wjiNewtonScalarBilinear_val (v w : WJISobolev.space) :
    wjiNewtonScalarBilinear v w = wjiNewtonScalar v.val w.val := rfl

private def differentiableFields : Submodule ℝ ScalarField where
  carrier := {f | Differentiable ℝ f}
  zero_mem' := by
    change Differentiable ℝ (fun _ : RSpace => (0 : ℝ))
    exact differentiable_const 0
  add_mem' := by
    intro f g hf hg
    change Differentiable ℝ f at hf
    change Differentiable ℝ g at hg
    change Differentiable ℝ (f + g)
    exact hf.add hg
  smul_mem' c f hf := by
    change Differentiable ℝ f at hf
    change Differentiable ℝ (fun x => c * f x)
    exact hf.const_mul c

private def gradientMap : differentiableFields →ₗ[ℝ] RInitial where
  toFun f := wjiScalarGradient f.val
  map_add' f g := by
    funext x i
    have hf : Differentiable ℝ f.val := f.property
    have hg : Differentiable ℝ g.val := g.property
    change (fderiv ℝ (fun y => f.val y + g.val y) x) (basisDirection i) = _
    rw [fderiv_fun_add (hf x) (hg x)] <;> rfl
  map_smul' c f := by
    funext x i
    have hf : Differentiable ℝ f.val := f.property
    change (fderiv ℝ (fun y => c * f.val y) x) (basisDirection i) = _
    rw [fderiv_const_mul (hf x) c] <;> rfl

private def gradientBilinear
    (hD : ∀ v w : Sob, Differentiable ℝ (wjiNewtonScalar v.val w.val)) :
    Sob →ₗ[ℝ] Sob →ₗ[ℝ] RInitial :=
  (restrictBilinear wjiNewtonScalarBilinear differentiableFields hD).compr₂ gradientMap

/-- The actual integral projection is bilinear by the L¹ integral laws and
the derivative laws on differentiable Newton potentials. -/
def wjiNewtonProjectedBilinear (hP : NewtonPoissonOn)
    (hD : ∀ v w : WJISobolev.space, Differentiable ℝ (wjiNewtonScalar v.val w.val)) :
    WJISobolev.space →ₗ[ℝ] WJISobolev.space →ₗ[ℝ] WJISobolev.space :=
  restrictBilinear (sobAdv.compr₂ WJISobolev.space.subtype + gradientBilinear hD)
    WJISobolev.space (wji_projectedTransport_mem hP)

theorem wjiNewtonProjectedBilinear_val (hP : NewtonPoissonOn)
    (hD : ∀ v w : WJISobolev.space, Differentiable ℝ (wjiNewtonScalar v.val w.val))
    (v w : WJISobolev.space) :
    (wjiNewtonProjectedBilinear hP hD v w).val = projectedTransport v.val w.val := rfl

/-- No abstract Leray-map assumption is used for the finite row expansion. -/
theorem wji_finiteExpansionLaw_of_newtonPoisson (hP : NewtonPoissonOn)
    (hD : ∀ v w : WJISobolev.space, Differentiable ℝ (wjiNewtonScalar v.val w.val)) (δ : ℝ) :
    FiniteExpansionLaw δ := by
  let D : JetOperatorDomain :=
    { space := WJISobolev.space
      profile_mem := WJISobolev.profile_mem
      heat := WJISmooth.heatOn WJISobolev.space WJISobolev.space_smooth WJISobolev.heat_mem
      heat_eq := fun _ => rfl
      projected := wjiNewtonProjectedBilinear hP hD
      projected_eq := wjiNewtonProjectedBilinear_val hP hD }
  exact D.finiteExpansionLaw δ

/-- The proved scalar differentiability removes the separate regularity
hypothesis from the finite expansion gate. -/
theorem wji_finiteExpansionLaw_of_scalar_poisson (hP : NewtonPoissonOn) (δ : ℝ) :
    FiniteExpansionLaw δ :=
  wji_finiteExpansionLaw_of_newtonPoisson hP wjiNewtonScalar_differentiable δ

end
end CondFeffA
