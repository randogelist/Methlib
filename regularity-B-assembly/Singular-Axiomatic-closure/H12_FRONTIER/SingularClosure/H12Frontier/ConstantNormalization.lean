import SingularClosure.H12Frontier.LiteratureConstants

/-! Exact normalization of the fixed admissible literature instance.
The theorem changes neither the datum nor viscosity nor the physical equation. -/
set_option autoImplicit false
set_option Elab.async true
namespace SingularClosure.H12Frontier
noncomputable section

theorem coefficient_normalization (K : ℝ) :
    (K / (2 * Real.sqrt Real.pi)) * Real.sqrt paperScale = K / Real.sqrt 2 := by
  have h2 : Real.sqrt (2 : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hp : 2 * Real.sqrt Real.pi ≠ 0 :=
    (mul_pos (by norm_num) (Real.sqrt_pos.mpr Real.pi_pos)).ne'
  apply (eq_div_iff h2).mpr
  calc
    _ = K * ((Real.sqrt 2 * Real.sqrt paperScale) / (2 * Real.sqrt Real.pi)) := by ring
    _ = K := by rw [sqrt_scale_relation, div_self hp, mul_one]

theorem coefficient_norm_identity (a : CriticalSobolev 1)
    (hz : SpectralMeanZero (criticalCoeff 1 a)) :
    frontierConstant * ‖a‖ =
      (literatureK2 / Real.sqrt 2) * paperNorm 1 a := by
  rw [nativeHhalf_norm a hz]
  change frontierConstant * (Real.sqrt paperScale * paperNorm 1 a) = _
  rw [← mul_assoc, frontierConstant, coefficient_normalization]

theorem FRONTIER_H12_SMALLNESS_IFF (ν : ℝ) (a : CriticalSobolev 1)
    (hz : SpectralMeanZero (criticalCoeff 1 a)) :
    paperNorm 1 a < (Real.sqrt 2 / literatureK2) * ν ↔
      frontierConstant * ‖a‖ < ν := by
  rw [coefficient_norm_identity a hz]
  have hC : 0 < literatureK2 / Real.sqrt 2 :=
    div_pos literatureK2_pos (Real.sqrt_pos.mpr (by norm_num))
  have heq : ν / (literatureK2 / Real.sqrt 2) =
      (Real.sqrt 2 / literatureK2) * ν := by
    field_simp [literatureK2_pos.ne', (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne']
    <;> ring
  rw [← heq, lt_div_iff₀ hC, mul_comm (paperNorm 1 a)]

theorem sqrt_paperEnergy (A : ℝ) (hA : 0 ≤ A) :
    Real.sqrt (A / (4 * Real.pi)) =
      Real.sqrt A / (2 * Real.sqrt Real.pi) := by
  have hp : 0 < 2 * Real.sqrt Real.pi :=
    mul_pos (by norm_num) (Real.sqrt_pos.mpr Real.pi_pos)
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _)
    (div_nonneg (Real.sqrt_nonneg _) hp.le)).mp
  rw [Real.sq_sqrt (div_nonneg hA (by positivity)), div_pow]
  simp only [mul_pow, Real.sq_sqrt hA, Real.sq_sqrt Real.pi_pos.le]
  norm_num

theorem FRONTIER_H12_ODI_NORMALIZATION
    (ν A B d : ℝ) (hA : 0 ≤ A) :
    (d / (4 * Real.pi) +
      (ν - literatureK2 * Real.sqrt (A / (4 * Real.pi))) * (B / (2 * Real.pi)) ≤ 0) ↔
    (d + 2 * (ν - frontierConstant * Real.sqrt A) * B ≤ 0) := by
  rw [sqrt_paperEnergy A hA]
  have hp : 0 < 4 * Real.pi := by positivity
  have heq : (4 * Real.pi) *
      (d / (4 * Real.pi) +
        (ν - literatureK2 * (Real.sqrt A / (2 * Real.sqrt Real.pi))) *
          (B / (2 * Real.pi))) =
      d + 2 * (ν - frontierConstant * Real.sqrt A) * B := by
    unfold frontierConstant
    field_simp [Real.pi_ne_zero, (Real.sqrt_pos.mpr Real.pi_pos).ne']
    <;> ring
  constructor
  · intro h
    have hm := mul_le_mul_of_nonneg_left h hp.le
    simpa only [heq, mul_zero] using hm
  · intro h
    apply (mul_le_mul_left hp).mp
    simpa only [heq, mul_zero] using h

theorem paperEnergy_hasDerivAt {A : ℝ → ℝ} {d t : ℝ}
    (h : HasDerivAt A d t) :
    HasDerivAt (fun τ => A τ / (4 * Real.pi)) (d / (4 * Real.pi)) t :=
  h.div_const (4 * Real.pi)

/-- E02: literal constant expression, native coefficient, and exact energy conversion. -/
theorem FRONTIER_H12_CONSTANT_NORMALIZATION :
    0 < literatureK2 ∧ 0 < frontierConstant ∧
    literatureK2 = Real.sqrt 2 * CSHalf * CSOne * CSZero / (2 * Real.pi) ∧
    frontierConstant = literatureK2 / (2 * Real.sqrt Real.pi) ∧
    (∀ a : CriticalSobolev 1, SpectralMeanZero (criticalCoeff 1 a) →
      frontierConstant * ‖a‖ = (literatureK2 / Real.sqrt 2) * paperNorm 1 a) ∧
    (∀ ν A B d : ℝ, 0 ≤ A →
      (d / (4 * Real.pi) +
        (ν - literatureK2 * Real.sqrt (A / (4 * Real.pi))) * (B / (2 * Real.pi)) ≤ 0) ↔
      (d + 2 * (ν - frontierConstant * Real.sqrt A) * B ≤ 0)) :=
  ⟨literatureK2_pos, frontierConstant_pos, rfl, rfl,
    coefficient_norm_identity, FRONTIER_H12_ODI_NORMALIZATION⟩

theorem literal_radius_strictly_enlarged (ν : ℝ) (hν : 0 < ν) :
    ν / literatureK2 < (Real.sqrt 2 / literatureK2) * ν := by
  have hs : (1 : ℝ) < Real.sqrt 2 := by
    have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hn := Real.sqrt_nonneg (2 : ℝ)
    nlinarith
  have h := mul_lt_mul_of_pos_right
    (div_lt_div_of_pos_right hs literatureK2_pos) hν
  simpa only [one_div, inv_mul_eq_div] using h

end
end SingularClosure.H12Frontier
