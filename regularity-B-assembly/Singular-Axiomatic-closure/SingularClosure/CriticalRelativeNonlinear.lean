import SingularClosure.CriticalH1Algebra

/-! Exact nonlinear polarization against a smooth solenoidal field.  The
rough field needs only physical L2 membership and scalar-gradient annihilation. -/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory
open scoped BigOperators ContDiff

namespace SingularClosure

noncomputable section

/-- The derivative of the kinetic potential gives the mixed transport term. -/
theorem critical_inner_gradient_norm_sq
    (u : Field) (hu : ContDiff ℝ ∞ u) (x z : Vec) :
    inner ℝ z (gradient (fun y => inner ℝ (u y) (u y)) x) =
      2 * inner ℝ (u x) ((fderiv ℝ u x) z) := by
  let f : Vec → ℝ := fun y => inner ℝ (u y) (u y)
  have hlinear (L : Vec →L[ℝ] ℝ) : L z = ∑ j : Fin 3, z j * L (unitVector j) := by
    have h := congrArg L (sum_coordinate_unitVector z)
    simpa only [map_sum, map_smul, smul_eq_mul] using h.symm
  have hd := (((hu.differentiable (by simp)) x).hasFDerivAt).inner ℝ
    (((hu.differentiable (by simp)) x).hasFDerivAt)
  have hD : fderiv ℝ f x z = 2 * inner ℝ (u x) ((fderiv ℝ u x) z) := by
    change fderiv ℝ (fun y => inner ℝ (u y) (u y)) x z = _
    rw [hd.fderiv]
    simp only [ContinuousLinearMap.comp_apply, fderivInnerCLM_apply,
      ContinuousLinearMap.prod_apply]
    rw [real_inner_comm ((fderiv ℝ u x) z) (u x)]
    ring
  calc
    _ = ∑ j : Fin 3, z j * fderiv ℝ f x (unitVector j) := by
      simp [f, gradient, PiLp.inner_apply, RCLike.inner_apply, mul_comm]
    _ = fderiv ℝ f x z := (hlinear _).symm
    _ = _ := hD

/-- Actual nonlinear cancellation in the relative-energy identity.  No weak
derivative or energy inequality is required for the rough velocity. -/
theorem CRITICAL_RELATIVE_NONLINEAR_IDENTITY
    (v u : Field) (hv : MemLp v 2 (volume.restrict unitCube))
    (hdiv : ∀ f : Vec → ℝ, ContDiff ℝ ∞ f → SpatialPeriodic f →
      physicalFieldInner v (gradient f) = 0)
    (hu : ContDiff ℝ ∞ u) (hup : SpatialPeriodic u)
    (hsol : ∀ x : Vec, divergence u x = 0) :
    criticalWeakTransport v u - physicalFieldInner v (convection u) =
      criticalWeakTransport (v - u) u := by
  let w : Field := v - u
  have hw : MemLp w 2 (volume.restrict unitCube) :=
    hv.sub (critical_continuous_memLp_cube u hu.continuous 2)
  have hwdiv : ∀ f : Vec → ℝ, ContDiff ℝ ∞ f → SpatialPeriodic f →
      physicalFieldInner w (gradient f) = 0 :=
    critical_gradient_annihilation_sub_smooth v u hv hdiv hu hup hsol
  let f : Vec → ℝ := fun x => inner ℝ (u x) (u x)
  have hf : ContDiff ℝ ∞ f := hu.inner ℝ hu
  have hfp : SpatialPeriodic f := by
    intro x i
    change inner ℝ (u (x + unitVector i)) (u (x + unitVector i)) = _
    rw [hup]
  have hpoint (x : Vec) : inner ℝ (w x) (gradient f x) =
      2 * inner ℝ (u x) ((fderiv ℝ u x) (w x)) :=
    critical_inner_gradient_norm_sq u hu x (w x)
  have hcross : IntegrableOn
      (fun x => inner ℝ (u x) ((fderiv ℝ u x) (w x))) unitCube volume := by
    have hi := (criticalWeakFieldInner_integrable w (gradient f) hw
      (criticalWeak_gradient_continuous f hf)).const_mul (1 / 2 : ℝ)
    convert hi using 1
    funext x
    rw [hpoint]
    ring
  have hzero : (∫ x in unitCube,
      inner ℝ (u x) ((fderiv ℝ u x) (w x))) = 0 := by
    have hz := hwdiv f hf hfp
    unfold physicalFieldInner at hz
    simp_rw [hpoint] at hz
    rw [integral_const_mul] at hz
    linarith
  have halgebra (x : Vec) :
      inner ℝ (v x) ((fderiv ℝ u x) (v x)) - inner ℝ (v x) (convection u x) =
        inner ℝ (w x) ((fderiv ℝ u x) (w x)) +
          inner ℝ (u x) ((fderiv ℝ u x) (w x)) := by
    simp only [w, Pi.sub_apply, map_sub, inner_sub_left, inner_sub_right, convection]
    ring
  calc
    _ = ∫ x in unitCube,
        inner ℝ (v x) ((fderiv ℝ u x) (v x)) - inner ℝ (v x) (convection u x) := by
      exact (integral_sub (criticalWeakTransport_integrable v u hv hu)
        (criticalWeakFieldInner_integrable v (convection u) hv
          (convection_continuous hu))).symm
    _ = ∫ x in unitCube,
        inner ℝ (w x) ((fderiv ℝ u x) (w x)) +
          inner ℝ (u x) ((fderiv ℝ u x) (w x)) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall halgebra
    _ = criticalWeakTransport w u +
        ∫ x in unitCube, inner ℝ (u x) ((fderiv ℝ u x) (w x)) :=
      integral_add (criticalWeakTransport_integrable w u hw hu) hcross
    _ = _ := by rw [hzero, add_zero]

end

end SingularClosure
