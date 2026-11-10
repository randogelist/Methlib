import NSE_NOH_Classical

/-!
# NSE_NOH FIX13: Pointwise kinetic and gradient energy decomposition

All results use actual differentiable spatial fields on the Euclidean
periodic-coordinate model. The L² distributional trace and the
integration over the physical torus are NOT proved by these identities.
The established classical NSE lifting is reused unchanged.
NO_LOCAL_LEAN: this is source preparation for external native Lean 4.33.0.
-/

set_option autoImplicit false
set_option maxHeartbeats 0

namespace NSE_NOH
noncomputable section

/-- Euclidean kinetic-energy density of a finite-component velocity. -/
def squareMassDensity (n : ℕ) (a : Vector n) : ℝ :=
  ∑ i : Fin n, (a i) ^ (2 : ℕ)

/-- Spatial Dirichlet density of a scalar field. -/
def scalarGradDensity (n : ℕ) (f : RSpace n → ℝ) (x : RSpace n) : ℝ :=
  ∑ j : Fin n, (coordinateDerivative n j f x) ^ (2 : ℕ)

/-- Sum of squared first spatial derivatives of all vector components. -/
def vectorGradDensity (n : ℕ) (u : RSpace n → Vector n) (x : RSpace n) : ℝ :=
  ∑ i : Fin n, scalarGradDensity n (fun y => u y i) x

/-- Exact kinetic mass density of the geometric 2D3C lift. -/
theorem squareMassDensity_liftedVelocity
    (w : ℝ → RSpace 2 → ℝ) (v : ℝ → RSpace 2 → Vector 2)
    (t : ℝ) (x : RSpace 3) :
    squareMassDensity 3 (liftedVelocity w v t x) =
      (w t (realProjection2 x)) ^ (2 : ℕ) +
        squareMassDensity 2 (v t (realProjection2 x)) := by
  simp only [squareMassDensity, Fin.sum_univ_three, Fin.sum_univ_two]
  change
      (w t (realProjection2 x)) ^ (2 : ℕ) +
        (v t (realProjection2 x) 0) ^ (2 : ℕ) +
          (v t (realProjection2 x) 1) ^ (2 : ℕ) =
      (w t (realProjection2 x)) ^ (2 : ℕ) +
        ((v t (realProjection2 x) 0) ^ (2 : ℕ) +
          (v t (realProjection2 x) 1) ^ (2 : ℕ))
  ring

/-- The first coordinate derivative vanishes; the remaining derivatives
are exactly the two derivatives of the planar scalar. -/
theorem scalarGradDensity_lift
    (f : RSpace 2 → ℝ) (x : RSpace 3)
    (hf : DifferentiableAt ℝ f (realProjection2 x)) :
    scalarGradDensity 3 (fun z => f (realProjection2 z)) x =
      scalarGradDensity 2 f (realProjection2 x) := by
  have h0 := coordinateDerivative_liftScalar_zero f x hf
  have h1 := coordinateDerivative_liftScalar_one f x hf
  have h2 := coordinateDerivative_liftScalar_two f x hf
  simp only [scalarGradDensity, Fin.sum_univ_three, Fin.sum_univ_two]
  rw [h0, h1, h2]
  ring

/-- Pointwise equality of the full 3D viscous quadratic form and
scalar plus planar 2D quadratic forms. This does not integrate the
identity or assert a time-zero derivative exists. -/
theorem vectorGradDensity_liftedVelocity
    (w : ℝ → RSpace 2 → ℝ) (v : ℝ → RSpace 2 → Vector 2)
    (t : ℝ) (x : RSpace 3)
    (hw : DifferentiableAt ℝ (w t) (realProjection2 x))
    (hv : ∀ i : Fin 2,
      DifferentiableAt ℝ (fun y : RSpace 2 => v t y i) (realProjection2 x)) :
    vectorGradDensity 3 (liftedVelocity w v t) x =
      scalarGradDensity 2 (w t) (realProjection2 x) +
        vectorGradDensity 2 (v t) (realProjection2 x) := by
  simp only [vectorGradDensity, Fin.sum_univ_three, Fin.sum_univ_two]
  change
    scalarGradDensity 3 (fun z => w t (realProjection2 z)) x +
      scalarGradDensity 3 (fun z => v t (realProjection2 z) 0) x +
        scalarGradDensity 3 (fun z => v t (realProjection2 z) 1) x =
    scalarGradDensity 2 (w t) (realProjection2 x) +
      (scalarGradDensity 2 (fun y => v t y 0) (realProjection2 x) +
        scalarGradDensity 2 (fun y => v t y 1) (realProjection2 x))
  rw [scalarGradDensity_lift (w t) x hw,
      scalarGradDensity_lift (fun y => v t y 0) x (hv 0),
      scalarGradDensity_lift (fun y => v t y 1) x (hv 1)]
  ring

/-- A single, pointwise mass-plus-dissipation decomposition.
The energy integral and its time derivative remain distinct targets. -/
theorem pointwiseEnergyDissipation_liftedVelocity
    (ν : ℝ) (w : ℝ → RSpace 2 → ℝ)
    (v : ℝ → RSpace 2 → Vector 2)
    (t : ℝ) (x : RSpace 3)
    (hw : DifferentiableAt ℝ (w t) (realProjection2 x))
    (hv : ∀ i : Fin 2,
      DifferentiableAt ℝ (fun y : RSpace 2 => v t y i) (realProjection2 x)) :
    squareMassDensity 3 (liftedVelocity w v t x) +
        2 * ν * vectorGradDensity 3 (liftedVelocity w v t) x =
      ((w t (realProjection2 x)) ^ (2 : ℕ) +
          2 * ν * scalarGradDensity 2 (w t) (realProjection2 x)) +
      (squareMassDensity 2 (v t (realProjection2 x)) +
          2 * ν * vectorGradDensity 2 (v t) (realProjection2 x)) := by
  rw [squareMassDensity_liftedVelocity,
      vectorGradDensity_liftedVelocity w v t x hw hv]
  ring

end
end NSE_NOH

#print axioms NSE_NOH.squareMassDensity_liftedVelocity
#print axioms NSE_NOH.scalarGradDensity_lift
#print axioms NSE_NOH.vectorGradDensity_liftedVelocity
#print axioms NSE_NOH.pointwiseEnergyDissipation_liftedVelocity
