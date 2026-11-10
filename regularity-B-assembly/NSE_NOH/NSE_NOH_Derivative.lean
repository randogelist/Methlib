import NSE_NOH_Jet

/-!
# NSE_NOH FIX9: first ACTUAL differentiable-function lift edge

The preceding `NSEJet_lift` theorem handles algebra of one-point jets.
This module begins the calculus link between the actual definitions of
`coordinateDerivative` and the planar spatial derivatives, using the
continuous linear projection R^3 -> R^2 and the fderiv chain rule.

No global PDE existence is asserted. The frozen NSE_NOH root and all
its L^2 trace/smoothing requirements remain unchanged.
External native Lean validation only; no local Lean was executed.
-/

set_option autoImplicit false
set_option maxHeartbeats 0

namespace NSE_NOH

noncomputable section

/- The existing coordinate projection as an ACTUAL continuous linear map. -/
def realProjection2CLM : RSpace 3 →L[ℝ] RSpace 2 :=
  ContinuousLinearMap.pi (fun i : Fin 2 =>
    ContinuousLinearMap.proj (R := ℝ) (Fin.succ i))

@[simp]
theorem realProjection2CLM_apply (x : RSpace 3) :
    realProjection2CLM x = realProjection2 x := by
  funext i
  rfl

/- Real fderiv of a lifted scalar function: the exact chain-rule formula. -/
theorem fderiv_liftScalar
    (f : RSpace 2 → ℝ) (x : RSpace 3)
    (hf : DifferentiableAt ℝ f (realProjection2 x)) :
    fderiv ℝ (fun y : RSpace 3 => f (realProjection2 y)) x =
      (fderiv ℝ f (realProjection2 x)).comp realProjection2CLM := by
  have heq : (fun y : RSpace 3 => f (realProjection2 y)) =
      f ∘ realProjection2CLM := by
    funext y
    simp [realProjection2CLM_apply]
  rw [heq]
  rw [fderiv_comp]
  · simp only [ContinuousLinearMap.fderiv, realProjection2CLM_apply]
  · simpa only [realProjection2CLM_apply] using hf
  · exact realProjection2CLM.differentiableAt

/- The absent x1-variable has ZERO directional derivative. -/
theorem coordinateDerivative_liftScalar_zero
    (f : RSpace 2 → ℝ) (x : RSpace 3)
    (hf : DifferentiableAt ℝ f (realProjection2 x)) :
    coordinateDerivative 3 0 (fun y => f (realProjection2 y)) x = 0 := by
  unfold coordinateDerivative
  rw [fderiv_liftScalar f x hf]
  have hvec :
      realProjection2CLM (fun j : Fin 3 => if j = (0 : Fin 3) then (1 : ℝ) else 0) =
        (0 : RSpace 2) := by
    funext i
    fin_cases i <;> rfl
  simp only [ContinuousLinearMap.comp_apply, hvec, map_zero]

/- The x2-derivative is the first planar derivative. -/
theorem coordinateDerivative_liftScalar_one
    (f : RSpace 2 → ℝ) (x : RSpace 3)
    (hf : DifferentiableAt ℝ f (realProjection2 x)) :
    coordinateDerivative 3 1 (fun y => f (realProjection2 y)) x =
      coordinateDerivative 2 0 f (realProjection2 x) := by
  unfold coordinateDerivative
  rw [fderiv_liftScalar f x hf]
  have hvec :
      realProjection2CLM (fun j : Fin 3 => if j = (1 : Fin 3) then (1 : ℝ) else 0) =
        (fun j : Fin 2 => if j = (0 : Fin 2) then (1 : ℝ) else 0) := by
    funext i
    fin_cases i <;> rfl
  simp only [ContinuousLinearMap.comp_apply, hvec]

/- The x3-derivative is the second planar derivative. -/
theorem coordinateDerivative_liftScalar_two
    (f : RSpace 2 → ℝ) (x : RSpace 3)
    (hf : DifferentiableAt ℝ f (realProjection2 x)) :
    coordinateDerivative 3 2 (fun y => f (realProjection2 y)) x =
      coordinateDerivative 2 1 f (realProjection2 x) := by
  unfold coordinateDerivative
  rw [fderiv_liftScalar f x hf]
  have hvec :
      realProjection2CLM (fun j : Fin 3 => if j = (2 : Fin 3) then (1 : ℝ) else 0) =
        (fun j : Fin 2 => if j = (1 : Fin 2) then (1 : ℝ) else 0) := by
    funext i
    fin_cases i <;> rfl
  simp only [ContinuousLinearMap.comp_apply, hvec]

/- Time derivatives are definitionally preserved by the spatial lift. -/
theorem deriv_liftedVelocity_scalar
    (w : ℝ → RSpace 2 → ℝ)
    (v : ℝ → RSpace 2 → Vector 2)
    (t : ℝ) (x : RSpace 3) :
    deriv (fun s : ℝ => liftedVelocity w v s x 0) t =
      deriv (fun s : ℝ => w s (realProjection2 x)) t := by
  rfl

theorem deriv_liftedVelocity_planar_zero
    (w : ℝ → RSpace 2 → ℝ)
    (v : ℝ → RSpace 2 → Vector 2)
    (t : ℝ) (x : RSpace 3) :
    deriv (fun s : ℝ => liftedVelocity w v s x 1) t =
      deriv (fun s : ℝ => v s (realProjection2 x) 0) t := by
  rfl

theorem deriv_liftedVelocity_planar_one
    (w : ℝ → RSpace 2 → ℝ)
    (v : ℝ → RSpace 2 → Vector 2)
    (t : ℝ) (x : RSpace 3) :
    deriv (fun s : ℝ => liftedVelocity w v s x 2) t =
      deriv (fun s : ℝ => v s (realProjection2 x) 1) t := by
  rfl

end
end NSE_NOH

#check NSE_NOH.realProjection2CLM
#print axioms NSE_NOH.realProjection2CLM_apply
#print axioms NSE_NOH.fderiv_liftScalar
#print axioms NSE_NOH.coordinateDerivative_liftScalar_zero
#print axioms NSE_NOH.coordinateDerivative_liftScalar_one
#print axioms NSE_NOH.coordinateDerivative_liftScalar_two
#print axioms NSE_NOH.deriv_liftedVelocity_scalar
#print axioms NSE_NOH.deriv_liftedVelocity_planar_zero
#print axioms NSE_NOH.deriv_liftedVelocity_planar_one
