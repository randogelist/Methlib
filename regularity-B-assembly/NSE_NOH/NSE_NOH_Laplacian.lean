import NSE_NOH_Derivative

/-!
# NSE_NOH FIX11: actual second-order spatial Laplacian lift

Concrete real Euclidean coordinate model associated with the periodic 2D3C
representative. No PDE existence or energy theorem is imported or asserted.

The regularity hypothesis `PlanarC2` is precisely the differentiability
needed to apply the existing first-order derivative lift twice. The
frozen NSE_NOH L² trace domain is not strengthened by this local lemma.
-/

set_option autoImplicit false
set_option maxHeartbeats 0

namespace NSE_NOH
noncomputable section

/- Each first coordinate derivative is differentiable, as is the function. -/
def PlanarC2 (f : RSpace 2 → ℝ) : Prop :=
  (∀ y : RSpace 2, DifferentiableAt ℝ f y) ∧
  (∀ j : Fin 2, ∀ y : RSpace 2,
    DifferentiableAt ℝ (coordinateDerivative 2 j f) y)

/- There is no x1-dependence, even after a second x1-derivative. -/
theorem secondDerivative_liftScalar_zero
    (f : RSpace 2 → ℝ) (x : RSpace 3)
    (hf : ∀ y : RSpace 2, DifferentiableAt ℝ f y) :
    coordinateDerivative 3 0
      (coordinateDerivative 3 0 (fun z : RSpace 3 => f (realProjection2 z))) x = 0 := by
  have hzero :
      coordinateDerivative 3 0 (fun z : RSpace 3 => f (realProjection2 z)) =
        (fun _ : RSpace 3 => (0 : ℝ)) := by
    funext y
    exact coordinateDerivative_liftScalar_zero f y (hf (realProjection2 y))
  rw [hzero]
  simp [coordinateDerivative, fderiv_const_apply]

/- The x2 second derivative is the y1 second derivative. -/
theorem secondDerivative_liftScalar_one
    (f : RSpace 2 → ℝ) (x : RSpace 3)
    (hf : ∀ y : RSpace 2, DifferentiableAt ℝ f y)
    (hf0 : DifferentiableAt ℝ (coordinateDerivative 2 0 f) (realProjection2 x)) :
    coordinateDerivative 3 1
      (coordinateDerivative 3 1 (fun z : RSpace 3 => f (realProjection2 z))) x =
    coordinateDerivative 2 0 (coordinateDerivative 2 0 f) (realProjection2 x) := by
  have hone :
      coordinateDerivative 3 1 (fun z : RSpace 3 => f (realProjection2 z)) =
        (fun y : RSpace 3 => coordinateDerivative 2 0 f (realProjection2 y)) := by
    funext y
    exact coordinateDerivative_liftScalar_one f y (hf (realProjection2 y))
  rw [hone]
  exact coordinateDerivative_liftScalar_one (coordinateDerivative 2 0 f) x hf0

/- The x3 second derivative is the y2 second derivative. -/
theorem secondDerivative_liftScalar_two
    (f : RSpace 2 → ℝ) (x : RSpace 3)
    (hf : ∀ y : RSpace 2, DifferentiableAt ℝ f y)
    (hf1 : DifferentiableAt ℝ (coordinateDerivative 2 1 f) (realProjection2 x)) :
    coordinateDerivative 3 2
      (coordinateDerivative 3 2 (fun z : RSpace 3 => f (realProjection2 z))) x =
    coordinateDerivative 2 1 (coordinateDerivative 2 1 f) (realProjection2 x) := by
  have htwo :
      coordinateDerivative 3 2 (fun z : RSpace 3 => f (realProjection2 z)) =
        (fun y : RSpace 3 => coordinateDerivative 2 1 f (realProjection2 y)) := by
    funext y
    exact coordinateDerivative_liftScalar_two f y (hf (realProjection2 y))
  rw [htwo]
  exact coordinateDerivative_liftScalar_two (coordinateDerivative 2 1 f) x hf1

/- The exact full spatial Laplacian of a lifted scalar field. -/
theorem spatialLaplacian_liftScalar
    (f : RSpace 2 → ℝ) (x : RSpace 3) (hf : PlanarC2 f) :
    spatialLaplacian 3 (fun z : RSpace 3 => f (realProjection2 z)) x =
      spatialLaplacian 2 f (realProjection2 x) := by
  have h0 := secondDerivative_liftScalar_zero f x hf.1
  have h1 := secondDerivative_liftScalar_one f x hf.1 (hf.2 0 (realProjection2 x))
  have h2 := secondDerivative_liftScalar_two f x hf.1 (hf.2 1 (realProjection2 x))
  -- Expand the *finite* sums directly. The FIX10 use of
  -- `Fin.sum_univ_succ` left residual Fin 0 sums in the goal.
  -- Using exact Fin 3 / Fin 2 expansions preserves the actual
  -- Laplacian definition and the previously proved second derivatives.
  simp only [spatialLaplacian, Fin.sum_univ_three, Fin.sum_univ_two]
  rw [h0, h1, h2]
  ring

end
end NSE_NOH

#print axioms NSE_NOH.secondDerivative_liftScalar_zero
#print axioms NSE_NOH.secondDerivative_liftScalar_one
#print axioms NSE_NOH.secondDerivative_liftScalar_two
#print axioms NSE_NOH.spatialLaplacian_liftScalar
