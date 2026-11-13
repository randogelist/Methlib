import SingularClosure.H12Frontier.ProductConstants
import SingularClosure.H12Frontier.ConstantNormalization

/-! Exact product/public normalization; the mean-zero hypothesis is retained. -/
set_option autoImplicit false
set_option Elab.async true

namespace SingularClosure.H12Frontier
noncomputable section

theorem product_coefficient_normalization :
    nativeProduct * Real.sqrt paperScale =
      literatureK2 / (Real.sqrt 2 * paperScale ^ 3) := by
  have h2 : Real.sqrt (2 : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hs : paperScale ^ 3 ≠ 0 := pow_ne_zero 3 paperScale_pos.ne'
  apply (eq_div_iff (mul_ne_zero h2 hs)).mpr
  rw [product_literatureK2_eq]
  calc
    (nativeProduct * Real.sqrt paperScale) * (Real.sqrt 2 * paperScale ^ 3) =
        (Real.sqrt 2 * Real.sqrt paperScale) * paperScale ^ 3 * nativeProduct := by ring
    _ = 2 * Real.sqrt Real.pi * paperScale ^ 3 * nativeProduct := by
      rw [sqrt_scale_relation]

/-- P03: exact native-product coefficient identity in the existing public norm. -/
theorem PRODUCT_COEFFICIENT_NORM_IDENTITY (a : CriticalSobolev 1)
    (hz : SpectralMeanZero (criticalCoeff 1 a)) :
    nativeProduct * ‖a‖ =
      (literatureK2 / (Real.sqrt 2 * paperScale ^ 3)) * paperNorm 1 a := by
  rw [nativeHhalf_norm a hz]
  change nativeProduct * (Real.sqrt paperScale * paperNorm 1 a) = _
  rw [← mul_assoc, product_coefficient_normalization]

/-- P04: no datum, viscosity, equation, or fixed K2 is rescaled. -/
theorem PRODUCT_SMALLNESS_IFF (ν : ℝ) (a : CriticalSobolev 1)
    (hz : SpectralMeanZero (criticalCoeff 1 a)) :
    paperNorm 1 a < (Real.sqrt 2 * paperScale ^ 3 / literatureK2) * ν ↔
      nativeProduct * ‖a‖ < ν := by
  rw [PRODUCT_COEFFICIENT_NORM_IDENTITY a hz]
  have hC : 0 < literatureK2 / (Real.sqrt 2 * paperScale ^ 3) :=
    div_pos literatureK2_pos
      (mul_pos (Real.sqrt_pos.mpr (by norm_num)) (pow_pos paperScale_pos 3))
  have heq : ν / (literatureK2 / (Real.sqrt 2 * paperScale ^ 3)) =
      (Real.sqrt 2 * paperScale ^ 3 / literatureK2) * ν := by
    field_simp [literatureK2_pos.ne', paperScale_pos.ne',
      (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne']
    <;> ring
  rw [← heq, lt_div_iff₀ hC, mul_comm (paperNorm 1 a)]

theorem product_scale_cube_gt_one : 1 < paperScale ^ 3 := by
  have hs : 1 < paperScale := by
    unfold paperScale
    linarith [Real.pi_gt_three]
  have h2 : 1 < paperScale * paperScale :=
    hs.trans (by simpa only [mul_one] using mul_lt_mul_of_pos_left hs paperScale_pos)
  have h3 : paperScale * paperScale < paperScale * paperScale * paperScale := by
    simpa only [mul_one] using
      mul_lt_mul_of_pos_left hs (mul_pos paperScale_pos paperScale_pos)
  have hcube : paperScale ^ 3 = paperScale * paperScale * paperScale := by ring
  rw [hcube]
  exact h2.trans h3

/-- Exact strict gain over the fixed frontier coefficient. -/
theorem PRODUCT_RADIUS_RATIO (ν : ℝ) (hν : 0 < ν) :
    ν / nativeProduct = paperScale ^ 3 * (ν / frontierConstant) ∧
    ν / frontierConstant < ν / nativeProduct := by
  have heq : ν / nativeProduct = paperScale ^ 3 * (ν / frontierConstant) := by
    rw [frontierConstant_eq_nativeProduct]
    field_simp [nativeProduct_pos.ne', paperScale_pos.ne']
    <;> ring
  refine ⟨heq, ?_⟩
  rw [heq]
  simpa only [one_mul] using
    mul_lt_mul_of_pos_right product_scale_cube_gt_one (div_pos hν frontierConstant_pos)

end
end SingularClosure.H12Frontier
