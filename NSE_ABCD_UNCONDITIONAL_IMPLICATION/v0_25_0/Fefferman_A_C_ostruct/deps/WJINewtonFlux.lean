import Mathlib
import WJINewtonDifferentiate

namespace CondFeffA

open MeasureTheory Set Metric Filter Fefferman.ConcreteReal
open scoped Topology
noncomputable section

abbrev NewtonE3 := EuclideanSpace ℝ (Fin 3)

/-- Surface measure of the unit Euclidean sphere from the Haar disintegration.
    This uses the Euclidean norm for the sphere rather than the sup norm on
    the Pi presentation of space in the PDE package. -/
theorem newton_unit_sphere_mass :
    (volume : Measure NewtonE3).toSphere.real univ = 4 * Real.pi := by
  have hb : (volume : Measure NewtonE3).real (ball (0 : NewtonE3) 1) =
      Real.pi * 4 / 3 := by
    rw [measureReal_def, EuclideanSpace.volume_ball_fin_three]
    simp [ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi * 4 / 3)]
  rw [Measure.toSphere_real_apply_univ, hb]
  have dim : Module.finrank ℝ NewtonE3 = 3 := by simp [NewtonE3]
  rw [dim]
  push_cast
  ring

/-- Integrating the directional derivative of a compact test along any
    outward unit ray gives minus the value of the same test at the origin. -/
theorem newton_ray_derivative_integral {φ : NewtonE3 → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) (ω : sphere (0 : NewtonE3) 1) :
    (∫ r in Ioi (0 : ℝ), fderiv ℝ φ (r • (ω : NewtonE3)) ω) = -φ 0 := by
  let L : ℝ →L[ℝ] NewtonE3 := (ContinuousLinearMap.id ℝ ℝ).smulRight (ω : NewtonE3)
  have hω : ‖(ω : NewtonE3)‖ = 1 := mem_sphere_zero_iff_norm.mp ω.property
  have hL : Isometry L := by
    apply isometry_iff_dist_eq.mpr
    intro t r
    rw [dist_eq_norm, ← map_sub, dist_eq_norm]
    change ‖(t-r) • (ω : NewtonE3)‖ = ‖t-r‖
    rw [norm_smul, hω, mul_one]
  have hcompact : HasCompactSupport (φ ∘ L) := by
    obtain ⟨K, hK, hk⟩ := exists_compact_iff_hasCompactSupport.mpr hc
    refine exists_compact_iff_hasCompactSupport.mp
      ⟨L ⁻¹' K, hL.isClosedEmbedding.isCompact_preimage hK, ?_⟩
    intro r hr
    exact hk (L r) hr
  have deriv_eq (r : ℝ) : deriv (φ ∘ L) r = fderiv ℝ φ (r • (ω : NewtonE3)) ω := by
    have h := ((hφ.differentiable one_ne_zero (L r)).hasFDerivAt.comp r L.hasFDerivAt).hasDerivAt
    simpa [L] using h.deriv
  calc
    _ = ∫ r in Ioi (0 : ℝ), deriv (φ ∘ L) r := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r hr
      exact (deriv_eq r).symm
    _ = -(φ ∘ L) 0 := hcompact.integral_Ioi_deriv_eq (hφ.comp L.contDiff) 0
    _ = _ := by simp

/-- The radial integral left by pairing the Newton gradient with the gradient
    of a test function already has the exact Dirac normalization. -/
theorem newton_polar_flux_normalized {φ : NewtonE3 → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) :
    (∫ ω : sphere (0 : NewtonE3) 1,
      (-(4 * Real.pi)⁻¹) * (∫ r in Ioi (0 : ℝ),
        fderiv ℝ φ (r • (ω : NewtonE3)) ω)
      ∂(volume : Measure NewtonE3).toSphere) = φ 0 := by
  simp_rw [newton_ray_derivative_integral hφ hc]
  rw [integral_const, smul_eq_mul, newton_unit_sphere_mass]
  field_simp [Real.pi_ne_zero] <;> ring

/-- The Newton flux paired with the differential of a scalar test at z.
    The totalized value at z=0 is immaterial under Lebesgue measure. -/
def newtonTestFlux (φ : NewtonE3 → ℝ) (z : NewtonE3) : ℝ :=
  -(4 * Real.pi)⁻¹ * (fderiv ℝ φ z z / ‖z‖^3)

theorem newtonTestFlux_integrable {φ : NewtonE3 → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) : Integrable (newtonTestFlux φ) := by
  have hcont := hφ.continuous_fderiv one_ne_zero
  obtain ⟨M, hM⟩ := hcont.bounded_above_of_compact_support (hc.fderiv ℝ)
  have dim : Module.finrank ℝ NewtonE3 = 3 := by simp [NewtonE3]
  have hl : LocallyIntegrable (newtonTestFlux φ) volume := by
    apply locallyIntegrable_of_norm_le_rpow (E := NewtonE3) (f := newtonTestFlux φ)
      (μ := volume) (α := (2 : ℝ)) (C := (4*Real.pi)⁻¹*M)
      (by rw [dim]; decide) (by rw [dim]; norm_num)
    · apply Eventually.of_forall
      intro z
      by_cases hz : z = 0
      · subst z
        norm_num [newtonTestFlux]
      have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
      have hp : (0 : ℝ) ≤ (4 * Real.pi)⁻¹ := by positivity
      have hop : ‖fderiv ℝ φ z z‖ ≤ M * ‖z‖ :=
        ((fderiv ℝ φ z).le_opNorm z).trans (mul_le_mul_of_nonneg_right (hM z) hn.le)
      rw [newtonTestFlux, norm_mul, norm_neg, Real.norm_of_nonneg hp, norm_div,
        Real.norm_of_nonneg (pow_nonneg hn.le 3), Real.rpow_neg hn.le, Real.rpow_two]
      calc
        _ ≤ (4 * Real.pi)⁻¹ * (M * ‖z‖ / ‖z‖^3) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hop (pow_nonneg hn.le _)) hp
        _ = _ := by field_simp [hn.ne', Real.pi_ne_zero] <;> ring
    · apply Measurable.aestronglyMeasurable
      unfold newtonTestFlux
      fun_prop
  obtain ⟨K, hK, hzero⟩ := exists_compact_iff_hasCompactSupport.mpr (hc.fderiv ℝ)
  apply (hl.integrableOn_isCompact hK).integrable_of_forall_notMem_eq_zero
  intro z hz
  simp [newtonTestFlux, hzero z hz]

private theorem polar_integral (F : NewtonE3 → ℝ) (hi : Integrable F) :
    (∫ z, F z) = ∫ ω : sphere (0 : NewtonE3) 1,
      ∫ r : Ioi (0 : ℝ), F (r.val • ω.val) ∂Measure.volumeIoiPow 2
      ∂(volume : Measure NewtonE3).toSphere := by
  let μ : Measure NewtonE3 := volume
  let e := homeomorphUnitSphereProd NewtonE3
  let H := fun p : sphere (0 : NewtonE3) 1 × Ioi (0 : ℝ) =>
    F (e.symm p).val
  have dim : Module.finrank ℝ NewtonE3 - 1 = 2 := by simp [NewtonE3]
  have hs : Integrable (fun z : ({0}ᶜ : Set NewtonE3) => F z.val) (μ.comap (↑)) :=
    (integrableOn_iff_comap_subtypeVal (measurableSet_singleton _).compl).mp hi.integrableOn
  have hH : Integrable H (μ.toSphere.prod (Measure.volumeIoiPow (Module.finrank ℝ NewtonE3 - 1))) := by
    apply (μ.measurePreserving_homeomorphUnitSphereProd.integrable_comp_emb e.measurableEmbedding).mp
    change Integrable (fun z : ({0}ᶜ : Set NewtonE3) => F ((e.symm (e z)).val)) (μ.comap (↑))
    simpa only [e.symm_apply_apply] using hs
  calc
    (∫ z, F z) = ∫ z : ({0}ᶜ : Set NewtonE3), F z.val ∂(μ.comap (↑)) := by
      rw [integral_subtype_comap (measurableSet_singleton _).compl F, restrict_compl_singleton]
    _ = ∫ p, H p ∂μ.toSphere.prod (Measure.volumeIoiPow (Module.finrank ℝ NewtonE3 - 1)) := by
      have hx := μ.measurePreserving_homeomorphUnitSphereProd.integral_comp e.measurableEmbedding H
      change (∫ z : ({0}ᶜ : Set NewtonE3), H (e z) ∂(μ.comap (↑))) = _ at hx
      simpa only [H, e.symm_apply_apply] using hx
    _ = ∫ ω, ∫ r, H (ω,r) ∂Measure.volumeIoiPow (Module.finrank ℝ NewtonE3 - 1) ∂μ.toSphere :=
      integral_prod H hH
    _ = _ := by rw [dim] <;> rfl

private theorem integral_positive_density (f : ℝ → ℝ) :
    (∫ r : Ioi (0 : ℝ), f r.val ∂Measure.volumeIoiPow 2) =
      ∫ r in Ioi (0 : ℝ), r^2 * f r := by
  simp only [Measure.volumeIoiPow, ENNReal.ofReal]
  rw [integral_withDensity_eq_integral_smul,
    integral_subtype_comap measurableSet_Ioi (fun r : ℝ => Real.toNNReal (r^2) • f r)]
  · apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    change (r^2).toNNReal • f r = r^2 * f r
    rw [NNReal.smul_def, Real.coe_toNNReal _ (sq_nonneg r), smul_eq_mul]
  · exact (measurable_subtype_coe.pow_const (2 : ℕ)).real_toNNReal

private theorem newton_flux_on_ray (φ : NewtonE3 → ℝ) (ω : sphere (0 : NewtonE3) 1) :
    (∫ r : Ioi (0 : ℝ), newtonTestFlux φ (r.val • ω.val) ∂Measure.volumeIoiPow 2) =
      -(4*Real.pi)⁻¹ * ∫ r in Ioi (0 : ℝ), fderiv ℝ φ (r • ω.val) ω.val := by
  rw [integral_positive_density (fun r : ℝ => newtonTestFlux φ (r • ω.val)), ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  have hr' : 0 < r := hr
  have hω : ‖ω.val‖ = 1 := mem_sphere_zero_iff_norm.mp ω.property
  simp only [newtonTestFlux, norm_smul, Real.norm_of_nonneg hr'.le, hω, mul_one,
    map_smul, smul_eq_mul]
  field_simp [hr'.ne', Real.pi_ne_zero] <;> ring

/-- The inverse-square radial flux of the Newton kernel has precisely one
    point source at the origin when paired against any compact C¹ test. -/
theorem newton_weak_flux_eq_evaluation {φ : NewtonE3 → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) :
    (∫ z, newtonTestFlux φ z) = φ 0 := by
  rw [polar_integral _ (newtonTestFlux_integrable hφ hc)]
  simp_rw [newton_flux_on_ray]
  exact newton_polar_flux_normalized hφ hc

/-- Identify the Euclidean radial coordinate with the actual package
    radius; the ambient norm in `RSpace` itself is the sup norm. -/
theorem newtonRadius_ofEuclidean (z : NewtonE3) :
    euclideanNorm3 (EuclideanSpace.equiv (Fin 3) ℝ z) = ‖z‖ := by
  rw [EuclideanSpace.norm_eq]
  change Real.sqrt (z 0 * z 0 + z 1 * z 1 + z 2 * z 2) =
    Real.sqrt (∑ i : Fin 3, ‖z i‖^2)
  simp only [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs]
  simp only [pow_two]

private theorem newton_radial_basis (z : RSpace) :
    z = z 0 • basisDirection 0 + z 1 • basisDirection 1 + z 2 • basisDirection 2 := by
  funext i
  fin_cases i
  · change z 0 = z 0 * 1 + z 1 * 0 + z 2 * 0
    ring
  · change z 1 = z 0 * 0 + z 1 * 1 + z 2 * 0
    ring
  · change z 2 = z 0 * 0 + z 1 * 0 + z 2 * 1
    ring

private theorem newton_radial_apply (z : RSpace) (L : RSpace →L[ℝ] ℝ) :
    L z = z 0 * L (basisDirection 0) + z 1 * L (basisDirection 1) + z 2 * L (basisDirection 2) := by
  calc
    _ = L (z 0 • basisDirection 0 + z 1 • basisDirection 1 + z 2 • basisDirection 2) :=
      congrArg (fun y : RSpace => L y) (newton_radial_basis z)
    _ = _ := by simp only [map_add, map_smul, smul_eq_mul]

/-- Flux identity with the three coordinate kernels and spatial derivatives
    used by `CondRecurrence`. -/
theorem newton_weak_flux_pkg {φ : RSpace → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) :
    (∫ z, newtonGradientKernel 0 z * spatialDerivative 0 φ z +
          newtonGradientKernel 1 z * spatialDerivative 1 φ z +
          newtonGradientKernel 2 z * spatialDerivative 2 φ z) = φ 0 := by
  let e := EuclideanSpace.equiv (Fin 3) ℝ
  let G := fun z : RSpace => newtonGradientKernel 0 z * spatialDerivative 0 φ z +
      newtonGradientKernel 1 z * spatialDerivative 1 φ z +
      newtonGradientKernel 2 z * spatialDerivative 2 φ z
  have hcm : HasCompactSupport (φ ∘ e) := by
    obtain ⟨K, hK, hk⟩ := exists_compact_iff_hasCompactSupport.mpr hc
    exact exists_compact_iff_hasCompactSupport.mp
      ⟨e ⁻¹' K, e.toHomeomorph.isClosedEmbedding.isCompact_preimage hK, fun r hr => hk (e r) hr⟩
  have heq (z : NewtonE3) : G (e z) = newtonTestFlux (φ ∘ e) z := by
    have hd := ((hφ.differentiable one_ne_zero (e z)).hasFDerivAt).comp z e.hasFDerivAt
    unfold newtonTestFlux
    rw [hd.fderiv]
    change G (e z) = -(4 * Real.pi)⁻¹ * (fderiv ℝ φ (e z) (e z) / ‖z‖^3)
    rw [newton_radial_apply (e z) (fderiv ℝ φ (e z)), ← newtonRadius_ofEuclidean z]
    simp only [G, newtonGradientKernel, spatialDerivative, div_eq_mul_inv, mul_inv_rev]
    ring
  have hpres : MeasurePreserving e := PiLp.volume_preserving_ofLp (Fin 3)
  calc
    (∫ z, G z) = ∫ z : NewtonE3, G (e z) :=
      (hpres.integral_comp e.toHomeomorph.measurableEmbedding G).symm
    _ = ∫ z, newtonTestFlux (φ ∘ e) z := integral_congr_ae (Eventually.of_forall heq)
    _ = _ := by
      simpa only [Function.comp_apply, map_zero] using
        newton_weak_flux_eq_evaluation (hφ.comp e.contDiff) hcm

end
end CondFeffA
