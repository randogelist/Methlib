import SingularClosure.CriticalPeriodicIBP

/-! Pressure and convection cancellation for arbitrary smooth periodic fields. -/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory
open scoped BigOperators ContDiff

namespace SingularClosure

noncomputable section

/-- Actual scalar-gradient testing vanishes for every smooth periodic
solenoidal vector field. -/
theorem critical_smooth_integral_inner_gradient_eq_zero
    (v : Field) (f : Vec → ℝ)
    (hv : ContDiff ℝ ∞ v) (hf : ContDiff ℝ ∞ f)
    (hvp : SpatialPeriodic v) (hfp : SpatialPeriodic f)
    (hdiv : ∀ x : Vec, divergence v x = 0) :
    (∫ x in unitCube, inner ℝ (v x) (gradient f x)) = 0 := by
  let F : Fin 3 → Vec → ℝ := fun j x => v x j * f x
  have hF (j : Fin 3) : ContDiff ℝ ∞ (F j) :=
    (((EuclideanSpace.proj j : Vec →L[ℝ] ℝ).contDiff).comp hv).mul hf
  have hFp (j : Fin 3) : SpatialPeriodic (F j) := by
    intro x i
    change v (x + unitVector i) j * f (x + unitVector i) = v x j * f x
    rw [hvp, hfp]
  have hD (j : Fin 3) (x : Vec) :
      fderiv ℝ (F j) x (unitVector j) =
        v x j * fderiv ℝ f x (unitVector j) + coordinateDerivative v j x j * f x := by
    have hdv := (EuclideanSpace.proj j : Vec →L[ℝ] ℝ).hasFDerivAt.comp x
      ((hv.differentiable (by simp)) x).hasFDerivAt
    have hd := hdv.mul (((hf.differentiable (by simp)) x).hasFDerivAt)
    have hdf : fderiv ℝ (F j) x =
        v x j • fderiv ℝ f x + f x •
          ((EuclideanSpace.proj j : Vec →L[ℝ] ℝ).comp (fderiv ℝ v x)) := by
      simpa only [F, Function.comp_def, EuclideanSpace.coe_proj] using hd.fderiv
    rw [hdf]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.comp_apply, EuclideanSpace.coe_proj, smul_eq_mul,
      coordinateDerivative]
    ring
  have hpoint (x : Vec) :
      (∑ j : Fin 3, fderiv ℝ (F j) x (unitVector j)) =
        inner ℝ (v x) (gradient f x) := by
    simp_rw [hD]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul]
    change (∑ j : Fin 3, v x j * fderiv ℝ f x (unitVector j)) +
      divergence v x * f x = _
    rw [hdiv, zero_mul, add_zero]
    simp [gradient, PiLp.inner_apply, RCLike.inner_apply, mul_comm]
  have hzero : (∫ x in unitCube,
      ∑ j : Fin 3, fderiv ℝ (F j) x (unitVector j)) = 0 := by
    rw [integral_finsetSum Finset.univ (fun j _ =>
      (((hF j).continuous_fderiv (by simp)).clm_apply continuous_const).continuousOn.integrableOn_compact
        isCompact_unitCube)]
    apply Finset.sum_eq_zero
    intro j _
    exact critical_integral_real_directionalDerivative_eq_zero (F j) (hF j) (hFp j) j
  simpa only [hpoint] using hzero

/-- The actual convection is energy-skew for every smooth periodic
solenoidal field, independently of any Galerkin representation. -/
theorem critical_smooth_integral_inner_convection_eq_zero
    (u : Field) (hu : ContDiff ℝ ∞ u) (hup : SpatialPeriodic u)
    (hdiv : ∀ x : Vec, divergence u x = 0) :
    (∫ x in unitCube, inner ℝ (u x) (convection u x)) = 0 := by
  let f : Vec → ℝ := fun x => inner ℝ (u x) (u x)
  have hf : ContDiff ℝ ∞ f := hu.inner ℝ hu
  have hfp : SpatialPeriodic f := by
    intro x i
    change inner ℝ (u (x + unitVector i)) (u (x + unitVector i)) = _
    rw [hup]
  have hD (j : Fin 3) (x : Vec) :
      fderiv ℝ f x (unitVector j) = 2 * inner ℝ (u x) (coordinateDerivative u j x) := by
    have hd := (((hu.differentiable (by simp)) x).hasFDerivAt).inner ℝ
      (((hu.differentiable (by simp)) x).hasFDerivAt)
    change fderiv ℝ (fun y => inner ℝ (u y) (u y)) x (unitVector j) = _
    rw [hd.fderiv]
    simp only [ContinuousLinearMap.comp_apply, fderivInnerCLM_apply,
      ContinuousLinearMap.prod_apply, coordinateDerivative]
    rw [real_inner_comm (fderiv ℝ u x (unitVector j)) (u x)]
    ring
  have hpoint (x : Vec) : inner ℝ (u x) (gradient f x) =
      2 * inner ℝ (u x) (convection u x) := by
    calc
      _ = ∑ j : Fin 3, u x j * (2 * inner ℝ (u x) (coordinateDerivative u j x)) := by
        simp [gradient, PiLp.inner_apply, RCLike.inner_apply, hD, mul_comm]
      _ = 2 * (∑ j : Fin 3, u x j * inner ℝ (u x) (coordinateDerivative u j x)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = _ := by
        rw [convection_eq_sum_coordinateDerivative, inner_sum]
        simp only [inner_smul_right]
  have hzero := critical_smooth_integral_inner_gradient_eq_zero
    u f hu hf hup hfp hdiv
  simp_rw [hpoint] at hzero
  rw [integral_const_mul] at hzero
  linarith

end

end SingularClosure
