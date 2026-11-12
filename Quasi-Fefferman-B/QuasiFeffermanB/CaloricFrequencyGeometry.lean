import QuasiFeffermanB.CaloricFourierBridge

/-!
The literal integer-frequency Leray projection is the Hermitian transverse
projection for the real unit frequency.  The sharp symmetric multiplier is
therefore an estimate of the actual Fourier coefficient operator.
-/

set_option autoImplicit false
set_option Elab.async true

open scoped BigOperators
open SingularClosure

namespace QuasiFeffermanB
noncomputable section

def frequencyRadius (k : Frequency) : ℝ :=
  Real.sqrt (galerkinFreqSq k : ℝ)

def complexFrequency (k : Frequency) : EuclideanSpace ℂ (Fin 3) :=
  complexVec (fun i => (k i : ℂ))

def normalizedComplexFrequency (k : Frequency) : EuclideanSpace ℂ (Fin 3) :=
  (frequencyRadius k : ℂ)⁻¹ • complexFrequency k

theorem frequencyRadius_pos (k : Frequency) (hk : k ≠ 0) :
    0 < frequencyRadius k := by
  apply Real.sqrt_pos.mpr
  have h : (1 : ℝ) ≤ (galerkinFreqSq k : ℝ) := by
    exact_mod_cast galerkinFreqSq_ge_one_of_ne_zero k hk
  linarith

theorem frequencyRadius_sq (k : Frequency) :
    frequencyRadius k ^ 2 = (galerkinFreqSq k : ℝ) := by
  apply Real.sq_sqrt
  exact_mod_cast galerkinFreqSq_nonneg k

theorem complexFrequency_norm_sq (k : Frequency) :
    ‖complexFrequency k‖ ^ 2 = (galerkinFreqSq k : ℝ) := by
  rw [EuclideanSpace.norm_sq_eq]
  change (∑ i : Fin 3, ‖(k i : ℂ)‖ ^ 2) = _
  simp [galerkinFreqSq, Complex.norm_intCast, Int.cast_abs]

theorem complexFrequency_norm (k : Frequency) :
    ‖complexFrequency k‖ = frequencyRadius k := by
  have h := complexFrequency_norm_sq k
  have hr := frequencyRadius_sq k
  have hr0 : 0 ≤ frequencyRadius k := Real.sqrt_nonneg _
  nlinarith [norm_nonneg (complexFrequency k)]

theorem normalizedComplexFrequency_norm (k : Frequency) (hk : k ≠ 0) :
    ‖normalizedComplexFrequency k‖ = 1 := by
  have hr := frequencyRadius_pos k hk
  simp [normalizedComplexFrequency, norm_smul, complexFrequency_norm,
    abs_of_pos hr, ne_of_gt hr]

theorem complexFrequency_inner (k : Frequency) (z : Fin 3 → ℂ) :
    inner ℂ (complexFrequency k) (complexVec z) = frequencyDot k z := by
  simp [complexFrequency, complexVec, PiLp.inner_apply, RCLike.inner_apply,
    frequencyDot, mul_comm]

theorem normalizedComplexFrequency_inner (k : Frequency) (z : Fin 3 → ℂ) :
    inner ℂ (normalizedComplexFrequency k) (complexVec z) =
      (frequencyRadius k : ℂ)⁻¹ * frequencyDot k z := by
  simp [normalizedComplexFrequency, inner_smul_left, complexFrequency_inner]

theorem frequency_complex_square_sum_eq_radius_sq (k : Frequency) :
    (∑ i : Fin 3, (k i : ℂ) ^ 2) = (frequencyRadius k : ℂ) ^ 2 := by
  have h : (∑ i : Fin 3, (k i : ℝ) ^ 2) = frequencyRadius k ^ 2 := by
    rw [frequencyRadius_sq]
    simp [galerkinFreqSq]
  exact_mod_cast h

theorem coefficientLeray_eq_complexTransverse
    (k : Frequency) (hk : k ≠ 0) (z : Fin 3 → ℂ) :
    complexVec (coefficientLeray k z) =
      complexTransverse (normalizedComplexFrequency k) (complexVec z) := by
  have hr : (frequencyRadius k : ℂ) ≠ 0 := by
    exact_mod_cast (frequencyRadius_pos k hk).ne'
  have hdot : (∑ j : Fin 3, (k j : ℂ) * z j) = frequencyDot k z := by
    simp [frequencyDot, mul_comm]
  apply PiLp.ext
  intro i
  change coefficientLeray k z i =
    z i - inner ℂ (normalizedComplexFrequency k) (complexVec z) *
      ((frequencyRadius k : ℂ)⁻¹ * (k i : ℂ))
  rw [normalizedComplexFrequency_inner]
  simp only [coefficientLeray, if_neg hk, hdot,
    frequency_complex_square_sum_eq_radius_sq, Complex.ofReal_inv]
  field_simp [hr]
  <;> ring

theorem complexTransverse_smul
    (e z : EuclideanSpace ℂ (Fin 3)) (α : ℂ) :
    complexTransverse e (α • z) = α • complexTransverse e z := by
  simp [complexTransverse, inner_smul_right, smul_sub, smul_smul, mul_comm]

theorem symmetricFrequencyTensor_normalized
    (k : Frequency) (hk : k ≠ 0) (z w : Fin 3 → ℂ) :
    complexVec (symmetricFrequencyTensor k z w) =
      (frequencyRadius k : ℂ) •
        ((inner ℂ (normalizedComplexFrequency k) (complexVec z)) • complexVec w +
          (inner ℂ (normalizedComplexFrequency k) (complexVec w)) • complexVec z) := by
  have hr : (frequencyRadius k : ℂ) ≠ 0 := by
    exact_mod_cast (frequencyRadius_pos k hk).ne'
  rw [normalizedComplexFrequency_inner, normalizedComplexFrequency_inner]
  apply PiLp.ext
  intro i
  change frequencyDot k z * w i + frequencyDot k w * z i =
    (frequencyRadius k : ℂ) *
      ((frequencyRadius k : ℂ)⁻¹ * frequencyDot k z * w i +
        (frequencyRadius k : ℂ)⁻¹ * frequencyDot k w * z i)
  field_simp [hr]
  <;> ring

/-- The actual nonzero-mode Leray projection has the sharp symmetric constant
`|k|`, before the Fourier derivative factor `π` is inserted. -/
theorem coefficientLeray_symmetric_frequency_bound
    (k : Frequency) (hk : k ≠ 0) (z w : Fin 3 → ℂ) :
    complexVecNorm (coefficientLeray k (symmetricFrequencyTensor k z w)) ≤
      Real.sqrt (galerkinFreqSq k : ℝ) *
        (complexVecNorm z * complexVecNorm w) := by
  have hr := frequencyRadius_pos k hk
  rw [complexVecNorm_eq_norm, coefficientLeray_eq_complexTransverse k hk,
    symmetricFrequencyTensor_normalized k hk, complexTransverse_smul, norm_smul]
  have hn : ‖(frequencyRadius k : ℂ)‖ = frequencyRadius k := by
    simp [abs_of_pos hr]
  rw [hn, complexVecNorm_eq_norm, complexVecNorm_eq_norm]
  exact mul_le_mul_of_nonneg_left
    (SYMMETRIC_COMPLEX_LERAY_MULTIPLIER
      (normalizedComplexFrequency k) (complexVec z) (complexVec w)
      (normalizedComplexFrequency_norm k hk)) hr.le

theorem criticalFrequencyWeight_eq_two_pi_radius
    (k : Frequency) (hk : k ≠ 0) :
    criticalFrequencyWeight k =
      2 * Real.pi * Real.sqrt (galerkinFreqSq k : ℝ) := by
  rw [criticalFrequencyWeight, if_neg hk, laplacianFrequency,
    Real.sqrt_mul (sq_nonneg (2 * Real.pi)), Real.sqrt_sq_eq_abs,
    abs_of_pos (by positivity : 0 < 2 * Real.pi)]

end
end QuasiFeffermanB
