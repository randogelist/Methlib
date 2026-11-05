import WJISobolevSpace
import WJINewtonKernel

namespace CondFeffA

open Fefferman Fefferman.ConcreteReal MeasureTheory
open scoped BigOperators ContDiff
noncomputable section

def wjiScalarGradient (q : RSpace → ℝ) : RInitial :=
  fun x i => spatialDerivative i q x

def wjiNewtonScalar (v w : RInitial) : RSpace → ℝ :=
  newtonPotential (fieldDiv (transport v w))

theorem wji_projectedTransport_eq_transport_add_gradient (v w : RInitial) :
    projectedTransport v w = transport v w + wjiScalarGradient (wjiNewtonScalar v w) := rfl

theorem wji_div_gradient (q : RSpace → ℝ) :
    fieldDiv (wjiScalarGradient q) = laplacian realAnalysis q := rfl

/-- The package Newton potential and the proposed gradient convolution have
    absolutely integrable integrands on the actual transport sources. -/
theorem wji_newton_transport_integrands (v w : WJISobolev.space) (x : RSpace) :
    Integrable (fun y => fieldDiv (transport v.val w.val) y /
      (4 * Real.pi * euclideanNorm3 (x-y))) ∧
    ∀ i : Fin 3, Integrable (fun y => fieldDiv (transport v.val w.val) y *
      newtonGradientKernel i (x-y)) := by
  obtain ⟨M, hM⟩ := WJISobolev.transport_div_bounded v w
  have hint := WJISobolev.transport_div_integrable v w
  exact ⟨newtonIntegrand_integrable hint hM x,
    fun i => newtonGradientIntegrand_integrable hint hM i x⟩

theorem wji_newton_scalar_bounded (v w : WJISobolev.space) :
    ∃ C : ℝ, ∀ x : RSpace, ‖wjiNewtonScalar v.val w.val x‖ ≤ C := by
  obtain ⟨M, hM⟩ := WJISobolev.transport_div_bounded v w
  refine ⟨M * newtonLocalMass 1 + (∫ y, ‖fieldDiv (transport v.val w.val) y‖), fun x => ?_⟩
  exact newtonPotential_norm_le (WJISobolev.transport_div_integrable v w) hM x

/-- The classical scalar fundamental-solution statement on the actual
    transport sources. It entails Sobolev regularity of the gradient and the
    signed Poisson equation, before forming a vector-space projection. -/
def NewtonPoissonOn : Prop :=
  ∀ v w : WJISobolev.space,
    wjiScalarGradient (wjiNewtonScalar v.val w.val) ∈ WJISobolev.space ∧
    laplacian realAnalysis (wjiNewtonScalar v.val w.val) = -fieldDiv (transport v.val w.val)

/-- Smoothness of the coordinate gradient upgrades differentiability of
    the potential to all orders. No integrability of the potential is needed. -/
theorem wji_smooth_of_gradient_mem {q : RSpace → ℝ} (hd : Differentiable ℝ q)
    (hg : wjiScalarGradient q ∈ WJISobolev.space) : ContDiff ℝ ∞ q := by
  apply contDiff_infty_iff_fderiv.mpr
  refine ⟨hd, contDiff_clm_apply_iff.mpr ?_⟩
  intro v
  have hv : (∑ i : Fin 3, v i • basisDirection i) = v := by
    funext j
    simp [basisDirection, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_ite]
  have he : (fun x => (fderiv ℝ q x) v) =
      (fun x => ∑ i : Fin 3, v i * spatialDerivative i q x) := by
    funext x
    calc
      _ = (fderiv ℝ q x) (∑ i : Fin 3, v i • basisDirection i) :=
        congrArg (fun y => (fderiv ℝ q x) y) hv.symm
      _ = _ := by simp only [map_sum, map_smul, smul_eq_mul, spatialDerivative]
  rw [he]
  apply ContDiff.sum
  intro i _
  exact contDiff_const.mul (WJISobolev.scalar_smooth (hg i))

theorem wji_newton_scalar_smooth_of_differentiable (hN : NewtonPoissonOn)
    (hD : ∀ v w : WJISobolev.space, Differentiable ℝ (wjiNewtonScalar v.val w.val))
    (v w : WJISobolev.space) : ContDiff ℝ ∞ (wjiNewtonScalar v.val w.val) :=
  wji_smooth_of_gradient_mem (hD v w) (hN v w).1

theorem wji_projectedTransport_mem (h : NewtonPoissonOn) (v w : WJISobolev.space) :
    projectedTransport v.val w.val ∈ WJISobolev.space := by
  rw [wji_projectedTransport_eq_transport_add_gradient]
  exact WJISobolev.space.add_mem (WJISobolev.transport_mem v w) (h v w).1

private lemma div_add_sobolev {v w : RInitial} (hv : v ∈ WJISobolev.space)
    (hw : w ∈ WJISobolev.space) : fieldDiv (v+w) = fieldDiv v + fieldDiv w := by
  funext x
  have he (i : Fin 3) :
      spatialDerivative i (fun y => (v+w) y i) x =
        spatialDerivative i (fun y => v y i) x + spatialDerivative i (fun y => w y i) x := by
    let f : WJISmooth.scalarSpace := ⟨fun y => v y i, WJISobolev.scalar_smooth (hv i)⟩
    let g : WJISmooth.scalarSpace := ⟨fun y => w y i, WJISobolev.scalar_smooth (hw i)⟩
    exact congrArg (fun z : WJISmooth.scalarSpace => z.val x) ((WJISmooth.partialMap i).map_add f g)
  change spatialDerivative 0 (fun y => (v+w) y 0) x +
      spatialDerivative 1 (fun y => (v+w) y 1) x + spatialDerivative 2 (fun y => (v+w) y 2) x =
    (spatialDerivative 0 (fun y => v y 0) x + spatialDerivative 1 (fun y => v y 1) x +
      spatialDerivative 2 (fun y => v y 2) x) +
    (spatialDerivative 0 (fun y => w y 0) x + spatialDerivative 1 (fun y => w y 1) x +
      spatialDerivative 2 (fun y => w y 2) x)
  rw [he 0, he 1, he 2]
  ring

/-- The projected transport is genuinely divergence-free once the scalar
    potential solves its correctly signed Poisson equation. -/
theorem wji_newton_solenoidal (h : NewtonPoissonOn) (v w : WJISobolev.space) :
    fieldDiv (projectedTransport v.val w.val) = 0 := by
  rw [wji_projectedTransport_eq_transport_add_gradient,
    div_add_sobolev (v := transport v.val w.val) (w := wjiScalarGradient (wjiNewtonScalar v.val w.val))
      (WJISobolev.transport_mem v w) (h v w).1,
    wji_div_gradient, (h v w).2, add_neg_cancel]

end
end CondFeffA

#print axioms CondFeffA.wji_projectedTransport_eq_transport_add_gradient
#print axioms CondFeffA.wji_div_gradient
#print axioms CondFeffA.wji_projectedTransport_mem
#print axioms CondFeffA.wji_newton_solenoidal

#print axioms CondFeffA.wji_newton_transport_integrands
#print axioms CondFeffA.wji_newton_scalar_bounded
#print axioms CondFeffA.wji_smooth_of_gradient_mem
#print axioms CondFeffA.wji_newton_scalar_smooth_of_differentiable
