import SingularClosure.InitialCutoffBounds
import SingularClosure.SmoothFourierLaplacian
import SingularClosure.PhysicalEnergy

/-! Actual periodic integration by parts for arbitrary smooth physical fields.
These statements concern the literal cube integrals and the Mathlib derivatives.
No Galerkin support or coefficient representation is required. -/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory
open scoped BigOperators ContDiff

namespace SingularClosure

noncomputable section

/-- A real periodic directional derivative has zero cube integral. -/
theorem critical_integral_real_directionalDerivative_eq_zero
    (f : Vec → ℝ) (hf : ContDiff ℝ ∞ f) (hp : SpatialPeriodic f) (j : Fin 3) :
    (∫ x in unitCube, fderiv ℝ f x (unitVector j)) = 0 := by
  let F : Vec → ℂ := fun x => (f x : ℂ)
  have hF : ContDiff ℝ ∞ F := Complex.ofRealCLM.contDiff.comp hf
  have hFp : SpatialPeriodic F := by
    intro x i
    change (f (x + unitVector i) : ℂ) = (f x : ℂ)
    rw [hp]
  have hD (x : Vec) : fderiv ℝ F x (unitVector j) =
      (fderiv ℝ f x (unitVector j) : ℂ) := by
    have hd := Complex.ofRealCLM.hasFDerivAt.comp x
      ((hf.differentiable (by simp)) x).hasFDerivAt
    have hh := congrArg (fun L : Vec →L[ℝ] ℂ => L (unitVector j)) hd.fderiv
    simpa only [F, Function.comp_def, ContinuousLinearMap.comp_apply,
      Complex.ofRealCLM_apply] using hh
  have hzero := integral_unitCube_directionalDerivative_eq_zero F hF hFp j
  simp_rw [hD] at hzero
  rw [integral_complex_ofReal] at hzero
  exact_mod_cast hzero

/-- Periodic integration by parts for the physical real inner product. -/
theorem critical_integral_inner_coordinateDerivative
    (u v : Field) (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (hup : SpatialPeriodic u) (hvp : SpatialPeriodic v) (j : Fin 3) :
    (∫ x in unitCube, inner ℝ (u x) (coordinateDerivative v j x)) =
      -(∫ x in unitCube, inner ℝ (coordinateDerivative u j x) (v x)) := by
  have hprod : ContDiff ℝ ∞ (fun x => inner ℝ (u x) (v x)) := hu.inner ℝ hv
  have hperiod : SpatialPeriodic (fun x => inner ℝ (u x) (v x)) := by
    intro x i
    rw [hup, hvp]
  have hD (x : Vec) :
      fderiv ℝ (fun y => inner ℝ (u y) (v y)) x (unitVector j) =
        inner ℝ (u x) (coordinateDerivative v j x) +
          inner ℝ (coordinateDerivative u j x) (v x) := by
    have hd := (((hu.differentiable (by simp)) x).hasFDerivAt).inner ℝ
      (((hv.differentiable (by simp)) x).hasFDerivAt)
    rw [hd.fderiv]
    simp only [ContinuousLinearMap.comp_apply, fderivInnerCLM_apply,
      ContinuousLinearMap.prod_apply, coordinateDerivative]
  have hleft : IntegrableOn
      (fun x => inner ℝ (u x) (coordinateDerivative v j x)) unitCube volume :=
    (hu.continuous.inner (coordinateDerivative_continuous hv j)).continuousOn.integrableOn_compact
      isCompact_unitCube
  have hright : IntegrableOn
      (fun x => inner ℝ (coordinateDerivative u j x) (v x)) unitCube volume :=
    ((coordinateDerivative_continuous hu j).inner hv.continuous).continuousOn.integrableOn_compact
      isCompact_unitCube
  have hzero := critical_integral_real_directionalDerivative_eq_zero
    (fun x => inner ℝ (u x) (v x)) hprod hperiod j
  simp_rw [hD] at hzero
  rw [integral_add hleft hright] at hzero
  linarith

/-- The arbitrary smooth Laplacian is the negative gradient pairing. -/
theorem critical_integral_inner_laplacian
    (u v : Field) (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (hup : SpatialPeriodic u) (hvp : SpatialPeriodic v) :
    (∫ x in unitCube, inner ℝ (u x) (laplacian v x)) =
      -(∑ j : Fin 3, ∫ x in unitCube,
        inner ℝ (coordinateDerivative u j x) (coordinateDerivative v j x)) := by
  have hj (j : Fin 3) :
      (∫ x in unitCube,
        inner ℝ (u x) (coordinateDerivative (coordinateDerivative v j) j x)) =
      -(∫ x in unitCube,
        inner ℝ (coordinateDerivative u j x) (coordinateDerivative v j x)) :=
    critical_integral_inner_coordinateDerivative u (coordinateDerivative v j) hu
      (coordinateDerivative_smooth hv j) hup (coordinateDerivative_spatialPeriodic j v hvp) j
  change (∫ x in unitCube, inner ℝ (u x)
    (∑ j : Fin 3, coordinateDerivative (coordinateDerivative v j) j x)) = _
  simp_rw [inner_sum]
  rw [integral_finsetSum Finset.univ (fun j _ =>
    (hu.continuous.inner
      (coordinateDerivative_continuous (coordinateDerivative_smooth hv j) j)).continuousOn.integrableOn_compact
        isCompact_unitCube)]
  simp_rw [hj]
  simp only [Finset.sum_neg_distrib]

/-- The viscous term has exactly the physical dissipation sign. -/
theorem critical_integral_inner_laplacian_self
    (u : Field) (hu : ContDiff ℝ ∞ u) (hup : SpatialPeriodic u) :
    (∫ x in unitCube, inner ℝ (u x) (laplacian u x)) = -physicalDissipation u := by
  rw [critical_integral_inner_laplacian u u hu hu hup hup]
  congr 1
  simp_rw [real_inner_self_eq_norm_sq]
  change (∑ j : Fin 3, ∫ x in unitCube, ‖coordinateDerivative u j x‖ ^ 2) =
    ∫ x in unitCube, gradientSquareDensity u x
  simp_rw [gradientSquareDensity_eq_sum_norm_sq]
  exact (integral_finsetSum Finset.univ (fun j _ =>
    ((coordinateDerivative_continuous hu j).norm.pow 2).continuousOn.integrableOn_compact
      isCompact_unitCube)).symm

end

end SingularClosure
