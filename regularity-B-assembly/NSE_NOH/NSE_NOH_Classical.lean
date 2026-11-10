import NSE_NOH_Laplacian

/-!
# NSE_NOH FIX12: physical smooth-point PDE lifting, not only formal jets

Under explicit local C² spatial regularity, every actual 2D solution
of `ClassicalNSE` with one passive scalar satisfying
`ClassicalPassiveScalar` lifts to the exact 3D `ClassicalNSE`
pointwise. This is the concrete analytic reconstruction of the
nonlinear PDE at all strictly positive times, NOT a construction of
2D L² initial-data solutions or of a 3D global L² trace.
-/

set_option autoImplicit false
set_option maxHeartbeats 0

namespace NSE_NOH
noncomputable section

theorem valueJet_liftedVelocity
    (w : ℝ → RSpace 2 → ℝ) (v : ℝ → RSpace 2 → Vector 2)
    (t : ℝ) (x : RSpace 3) :
    liftedVelocity w v t x =
      jetLiftVelocity (w t (realProjection2 x)) (v t (realProjection2 x)) := by
  funext i
  fin_cases i <;> rfl

theorem timeJet_liftedVelocity
    (w : ℝ → RSpace 2 → ℝ) (v : ℝ → RSpace 2 → Vector 2)
    (t : ℝ) (x : RSpace 3) :
    (fun i : Fin 3 => deriv (fun s : ℝ => liftedVelocity w v s x i) t) =
      jetLiftVelocity
        (deriv (fun s : ℝ => w s (realProjection2 x)) t)
        (fun i : Fin 2 => deriv (fun s : ℝ => v s (realProjection2 x) i) t) := by
  funext i
  fin_cases i <;> rfl

/- Exact full 3x3 Jacobian, with its first (x1) derivative row zero. -/
theorem spatialJet_liftedVelocity
    (w : ℝ → RSpace 2 → ℝ) (v : ℝ → RSpace 2 → Vector 2)
    (t : ℝ) (x : RSpace 3)
    (hw : ∀ y : RSpace 2, DifferentiableAt ℝ (w t) y)
    (hv : ∀ i : Fin 2, ∀ y : RSpace 2,
      DifferentiableAt ℝ (fun z : RSpace 2 => v t z i) y) :
    (fun j : Fin 3 => fun i : Fin 3 =>
      coordinateDerivative 3 j (fun z : RSpace 3 => liftedVelocity w v t z i) x) =
    jetLiftSpatialGrad
      (fun j : Fin 2 => coordinateDerivative 2 j (w t) (realProjection2 x))
      (fun j : Fin 2 => fun i : Fin 2 =>
        coordinateDerivative 2 j (fun z : RSpace 2 => v t z i) (realProjection2 x)) := by
  funext j i
  fin_cases j <;> fin_cases i
  · change coordinateDerivative 3 0 (fun z => w t (realProjection2 z)) x = 0
    exact coordinateDerivative_liftScalar_zero (w t) x (hw (realProjection2 x))
  · change coordinateDerivative 3 0 (fun z => v t (realProjection2 z) 0) x = 0
    exact coordinateDerivative_liftScalar_zero (fun y => v t y 0) x (hv 0 (realProjection2 x))
  · change coordinateDerivative 3 0 (fun z => v t (realProjection2 z) 1) x = 0
    exact coordinateDerivative_liftScalar_zero (fun y => v t y 1) x (hv 1 (realProjection2 x))
  · change coordinateDerivative 3 1 (fun z => w t (realProjection2 z)) x =
      coordinateDerivative 2 0 (w t) (realProjection2 x)
    exact coordinateDerivative_liftScalar_one (w t) x (hw (realProjection2 x))
  · change coordinateDerivative 3 1 (fun z => v t (realProjection2 z) 0) x =
      coordinateDerivative 2 0 (fun y => v t y 0) (realProjection2 x)
    exact coordinateDerivative_liftScalar_one (fun y => v t y 0) x (hv 0 (realProjection2 x))
  · change coordinateDerivative 3 1 (fun z => v t (realProjection2 z) 1) x =
      coordinateDerivative 2 0 (fun y => v t y 1) (realProjection2 x)
    exact coordinateDerivative_liftScalar_one (fun y => v t y 1) x (hv 1 (realProjection2 x))
  · change coordinateDerivative 3 2 (fun z => w t (realProjection2 z)) x =
      coordinateDerivative 2 1 (w t) (realProjection2 x)
    exact coordinateDerivative_liftScalar_two (w t) x (hw (realProjection2 x))
  · change coordinateDerivative 3 2 (fun z => v t (realProjection2 z) 0) x =
      coordinateDerivative 2 1 (fun y => v t y 0) (realProjection2 x)
    exact coordinateDerivative_liftScalar_two (fun y => v t y 0) x (hv 0 (realProjection2 x))
  · change coordinateDerivative 3 2 (fun z => v t (realProjection2 z) 1) x =
      coordinateDerivative 2 1 (fun y => v t y 1) (realProjection2 x)
    exact coordinateDerivative_liftScalar_two (fun y => v t y 1) x (hv 1 (realProjection2 x))

/- Concrete pressure gradient under the 2D3C projection. -/
theorem pressureJet_liftedPressure
    (q : ℝ → RSpace 2 → ℝ) (t : ℝ) (x : RSpace 3)
    (hq : DifferentiableAt ℝ (q t) (realProjection2 x)) :
    (fun i : Fin 3 => coordinateDerivative 3 i (liftedPressure q t) x) =
      jetLiftVelocity 0
        (fun i : Fin 2 => coordinateDerivative 2 i (q t) (realProjection2 x)) := by
  funext i
  fin_cases i
  · change coordinateDerivative 3 0 (fun z => q t (realProjection2 z)) x = 0
    exact coordinateDerivative_liftScalar_zero (q t) x hq
  · change coordinateDerivative 3 1 (fun z => q t (realProjection2 z)) x =
      coordinateDerivative 2 0 (q t) (realProjection2 x)
    exact coordinateDerivative_liftScalar_one (q t) x hq
  · change coordinateDerivative 3 2 (fun z => q t (realProjection2 z)) x =
      coordinateDerivative 2 1 (q t) (realProjection2 x)
    exact coordinateDerivative_liftScalar_two (q t) x hq

/- Concrete 3D Laplacian of all three lifted velocity components. -/
theorem lapJet_liftedVelocity
    (w : ℝ → RSpace 2 → ℝ) (v : ℝ → RSpace 2 → Vector 2)
    (t : ℝ) (x : RSpace 3)
    (hw : PlanarC2 (w t))
    (hv : ∀ i : Fin 2, PlanarC2 (fun y : RSpace 2 => v t y i)) :
    (fun i : Fin 3 => spatialLaplacian 3
      (fun z : RSpace 3 => liftedVelocity w v t z i) x) =
      jetLiftVelocity
        (spatialLaplacian 2 (w t) (realProjection2 x))
        (fun i : Fin 2 => spatialLaplacian 2
          (fun y : RSpace 2 => v t y i) (realProjection2 x)) := by
  funext i
  fin_cases i
  · change spatialLaplacian 3 (fun z => w t (realProjection2 z)) x =
      spatialLaplacian 2 (w t) (realProjection2 x)
    exact spatialLaplacian_liftScalar (w t) x hw
  · change spatialLaplacian 3 (fun z => v t (realProjection2 z) 0) x =
      spatialLaplacian 2 (fun y => v t y 0) (realProjection2 x)
    exact spatialLaplacian_liftScalar (fun y => v t y 0) x (hv 0)
  · change spatialLaplacian 3 (fun z => v t (realProjection2 z) 1) x =
      spatialLaplacian 2 (fun y => v t y 1) (realProjection2 x)
    exact spatialLaplacian_liftScalar (fun y => v t y 1) x (hv 1)

/- Actual pointwise PDE lifting: the jet theorem is applied only after
   every jet value is identified with a derivative of actual functions.
   No existence of a rough-data solution follows from this theorem. -/
theorem ClassicalNSE_lift_of_planar
    (ν : ℝ)
    (w : ℝ → RSpace 2 → ℝ)
    (v : ℝ → RSpace 2 → Vector 2)
    (q : ℝ → RSpace 2 → ℝ)
    (hPlanar : ClassicalNSE 2 ν v q)
    (hPassive : ClassicalPassiveScalar ν v w)
    (hw : ∀ t : ℝ, 0 < t → PlanarC2 (w t))
    (hv : ∀ t : ℝ, 0 < t → ∀ i : Fin 2,
      PlanarC2 (fun y : RSpace 2 => v t y i))
    (hq : ∀ t : ℝ, 0 < t → ∀ y : RSpace 2,
      DifferentiableAt ℝ (q t) y) :
    ClassicalNSE 3 ν (liftedVelocity w v) (liftedPressure q) := by
  intro t ht x
  let y : RSpace 2 := realProjection2 x
  have hPlanarJet : NSEJet 2 ν
      (v t y)
      (fun i : Fin 2 => deriv (fun s : ℝ => v s y i) t)
      (fun j : Fin 2 => fun i : Fin 2 =>
        coordinateDerivative 2 j (fun z : RSpace 2 => v t z i) y)
      (fun i : Fin 2 => spatialLaplacian 2 (fun z => v t z i) y)
      (fun i : Fin 2 => coordinateDerivative 2 i (q t) y) := by
    exact hPlanar t ht y
  have hPassiveJet :
      deriv (fun s : ℝ => w s y) t +
        v t y 0 * coordinateDerivative 2 0 (w t) y +
        v t y 1 * coordinateDerivative 2 1 (w t) y =
          ν * spatialLaplacian 2 (w t) y := by
    -- The scalar equation uses dtW + (a + b), while the jet
    -- stores (dtW + a) + b. Normalize addition without changing
    -- the hypothesis, its conclusion, or the analytic PDE ports.
    simpa only [Fin.sum_univ_two, add_assoc] using (hPassive t ht y)
  have hLiftedJet : NSEJet 3 ν
      (jetLiftVelocity (w t y) (v t y))
      (jetLiftVelocity
        (deriv (fun s : ℝ => w s y) t)
        (fun i : Fin 2 => deriv (fun s : ℝ => v s y i) t))
      (jetLiftSpatialGrad
        (fun j : Fin 2 => coordinateDerivative 2 j (w t) y)
        (fun j : Fin 2 => fun i : Fin 2 =>
          coordinateDerivative 2 j (fun z : RSpace 2 => v t z i) y))
      (jetLiftVelocity
        (spatialLaplacian 2 (w t) y)
        (fun i : Fin 2 => spatialLaplacian 2 (fun z => v t z i) y))
      (jetLiftVelocity 0
        (fun i : Fin 2 => coordinateDerivative 2 i (q t) y)) := by
    exact NSEJet_lift ν (w t y)
      (deriv (fun s : ℝ => w s y) t)
      (spatialLaplacian 2 (w t) y)
      (v t y)
      (fun i : Fin 2 => deriv (fun s : ℝ => v s y i) t)
      (fun i : Fin 2 => spatialLaplacian 2 (fun z => v t z i) y)
      (fun i : Fin 2 => coordinateDerivative 2 i (q t) y)
      (fun i : Fin 2 => coordinateDerivative 2 i (w t) y)
      (fun j : Fin 2 => fun i : Fin 2 =>
        coordinateDerivative 2 j (fun z : RSpace 2 => v t z i) y)
      hPlanarJet hPassiveJet
  change NSEJet 3 ν
    (liftedVelocity w v t x)
    (fun i : Fin 3 => deriv (fun s : ℝ => liftedVelocity w v s x i) t)
    (fun j : Fin 3 => fun i : Fin 3 =>
      coordinateDerivative 3 j (fun z : RSpace 3 => liftedVelocity w v t z i) x)
    (fun i : Fin 3 => spatialLaplacian 3 (fun z : RSpace 3 =>
      liftedVelocity w v t z i) x)
    (fun i : Fin 3 => coordinateDerivative 3 i (liftedPressure q t) x)
  rw [valueJet_liftedVelocity w v t x,
      timeJet_liftedVelocity w v t x,
      spatialJet_liftedVelocity w v t x (hw t ht).1 (fun i => (hv t ht i).1),
      lapJet_liftedVelocity w v t x (hw t ht) (hv t ht),
      pressureJet_liftedPressure q t x (hq t ht y)]
  exact hLiftedJet

end
end NSE_NOH

#print axioms NSE_NOH.valueJet_liftedVelocity
#print axioms NSE_NOH.timeJet_liftedVelocity
#print axioms NSE_NOH.spatialJet_liftedVelocity
#print axioms NSE_NOH.pressureJet_liftedPressure
#print axioms NSE_NOH.lapJet_liftedVelocity
#print axioms NSE_NOH.ClassicalNSE_lift_of_planar
