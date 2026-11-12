import SingularClosure.H12Frontier.Normalization
import SingularClosure.H12Frontier.ExplicitNonlinear

/-! Literal dilation of the unit physical cube and its Lebesgue Lp norms.
The target cube has ordinary, not probability-normalized, Lebesgue measure. -/
set_option autoImplicit false
set_option Elab.async true
open Set MeasureTheory
open scoped ENNReal NNReal BigOperators Pointwise
namespace SingularClosure.H12Frontier
noncomputable section

def paperScale : ℝ := 2 * Real.pi

theorem paperScale_pos : 0 < paperScale := by unfold paperScale; positivity

theorem paperScale_one_le : 1 ≤ paperScale := by
  unfold paperScale
  linarith [Real.pi_gt_three]

def dilatedCube (r : ℝ) : Set Vec := r • unitCube

def dilatedField {E : Type*} (r : ℝ) (f : Vec → E) : Vec → E :=
  fun x => f (r⁻¹ • x)

theorem map_dilatedCube (r : ℝ) (hr : 0 < r) :
    Measure.map (fun x : Vec => r⁻¹ • x) (volume.restrict (dilatedCube r)) =
      ENNReal.ofReal (r ^ 3) • volume.restrict unitCube := by
  let e : Vec ≃ᵐ Vec :=
    (Homeomorph.smul (isUnit_iff_ne_zero.mpr (inv_ne_zero hr.ne')).unit).toMeasurableEquiv
  have hp : e ⁻¹' unitCube = dilatedCube r := by
    change (fun x : Vec => r⁻¹ • x) ⁻¹' unitCube = r • unitCube
    exact preimage_smul_inv₀ hr.ne' unitCube
  have hm : (volume : Measure Vec).map e = ENNReal.ofReal (r ^ 3) • volume := by
    change Measure.map (fun x : Vec => r⁻¹ • x) volume = _
    rw [Measure.map_addHaar_smul volume (inv_ne_zero hr.ne')]
    have hd : Module.finrank ℝ Vec = 3 := by simp [Vec]
    simp only [hd, inv_pow, inv_inv, abs_of_pos (pow_pos hr 3)]
  have h := e.restrict_map (volume : Measure Vec) unitCube
  rw [hp, hm, Measure.restrict_smul] at h
  exact h.symm

theorem dilated_eLpNorm {E : Type*} [NormedAddCommGroup E]
    [SecondCountableTopology E] (r : ℝ) (hr : 0 < r)
    (f : Vec → E) (hf : Continuous f) (p : ℝ≥0∞) :
    eLpNorm (dilatedField r f) p (volume.restrict (dilatedCube r)) =
      (ENNReal.ofReal (r ^ 3)) ^ (1 / p).toReal *
        eLpNorm f p (volume.restrict unitCube) := by
  have h := eLpNorm_map_measure
    (μ := volume.restrict (dilatedCube r)) (p := p)
    (f := fun x : Vec => r⁻¹ • x) (g := f)
    hf.aestronglyMeasurable (measurable_const_smul (r⁻¹)).aemeasurable
  change eLpNorm (f ∘ (fun x : Vec => r⁻¹ • x)) p
    (volume.restrict (dilatedCube r)) = _
  rw [← h, map_dilatedCube r hr,
    eLpNorm_smul_measure_of_ne_zero
      (ne_of_gt (ENNReal.ofReal_pos.mpr (pow_pos hr 3))) f p]
  rfl

theorem dilated_eLpNorm_three {E : Type*} [NormedAddCommGroup E]
    [SecondCountableTopology E] (r : ℝ) (hr : 0 < r)
    (f : Vec → E) (hf : Continuous f) :
    eLpNorm (dilatedField r f) 3 (volume.restrict (dilatedCube r)) =
      ENNReal.ofReal r * eLpNorm f 3 (volume.restrict unitCube) := by
  rw [dilated_eLpNorm r hr f hf]
  have hpow : (ENNReal.ofReal (r ^ 3)) ^ (1 / (3 : ℝ≥0∞)).toReal =
      ENNReal.ofReal r := by
    norm_num only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat]
    rw [ENNReal.ofReal_pow hr.le, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  rw [hpow]

theorem dilated_eLpNorm_six {E : Type*} [NormedAddCommGroup E]
    [SecondCountableTopology E] (r : ℝ) (hr : 0 < r)
    (f : Vec → E) (hf : Continuous f) :
    eLpNorm (dilatedField r f) 6 (volume.restrict (dilatedCube r)) =
      ENNReal.ofReal (Real.sqrt r) * eLpNorm f 6 (volume.restrict unitCube) := by
  rw [dilated_eLpNorm r hr f hf]
  have hpow : (ENNReal.ofReal (r ^ 3)) ^ (1 / (6 : ℝ≥0∞)).toReal =
      ENNReal.ofReal (Real.sqrt r) := by
    norm_num only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat]
    rw [ENNReal.ofReal_pow hr.le, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num only [show (3 : ℝ) * (1 / 6) = 1 / 2 by norm_num]
    rw [Real.sqrt_eq_rpow, ENNReal.ofReal_rpow_of_nonneg hr.le (by norm_num)]
  rw [hpow]

theorem dilated_eLpNorm_two {E : Type*} [NormedAddCommGroup E]
    [SecondCountableTopology E] (r : ℝ) (hr : 0 < r)
    (f : Vec → E) (hf : Continuous f) :
    eLpNorm (dilatedField r f) 2 (volume.restrict (dilatedCube r)) =
      ENNReal.ofReal (r * Real.sqrt r) *
        eLpNorm f 2 (volume.restrict unitCube) := by
  rw [dilated_eLpNorm r hr f hf]
  have hroot : Real.sqrt (r ^ 3) = r * Real.sqrt r := by
    apply (sq_eq_sq₀ (Real.sqrt_nonneg _)
      (mul_nonneg hr.le (Real.sqrt_nonneg _))).mp
    rw [Real.sq_sqrt (pow_nonneg hr.le 3)]
    simp only [mul_pow, Real.sq_sqrt hr.le]
    ring
  have hpow : (ENNReal.ofReal (r ^ 3)) ^ (1 / (2 : ℝ≥0∞)).toReal =
      ENNReal.ofReal (r * Real.sqrt r) := by
    norm_num only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat]
    rw [ENNReal.ofReal_rpow_of_nonneg (pow_nonneg hr.le 3) (by norm_num),
      ← Real.sqrt_eq_rpow, hroot]
  rw [hpow]

/-- Literal coordinate description of the dilated fundamental cube. -/
theorem mem_dilatedCube_iff (r : ℝ) (hr : 0 < r) (x : Vec) :
    x ∈ dilatedCube r ↔ ∀ i : Fin 3, 0 ≤ x i ∧ x i ≤ r := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    intro i
    change 0 ≤ r * y i ∧ r * y i ≤ r
    exact ⟨mul_nonneg hr.le (hy i).1,
      (mul_le_mul_of_nonneg_left (hy i).2 hr.le).trans_eq (mul_one r)⟩
  · intro hx
    refine ⟨r⁻¹ • x, ?_, ?_⟩
    · intro i
      change 0 ≤ r⁻¹ * x i ∧ r⁻¹ * x i ≤ 1
      refine ⟨mul_nonneg (inv_nonneg.mpr hr.le) (hx i).1, ?_⟩
      have h := mul_le_mul_of_nonneg_left (hx i).2 (inv_nonneg.mpr hr.le)
      simpa only [inv_mul_cancel₀ hr.ne'] using h
    · simp only [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]

def paperCharacter (k : Frequency) (x : Vec) : ℂ :=
  Complex.exp (((∑ i : Fin 3, (k i : ℝ) * x i : ℝ) : ℂ) * Complex.I)

theorem fourierCharacter_dilated (k : Frequency) (x : Vec) :
    fourierCharacter k (paperScale⁻¹ • x) = paperCharacter k x := by
  have hsum : (∑ i : Fin 3, (k i : ℝ) * (paperScale⁻¹ • x) i) =
      paperScale⁻¹ * ∑ i : Fin 3, (k i : ℝ) * x i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    change (k i : ℝ) * (paperScale⁻¹ * x i) = paperScale⁻¹ * ((k i : ℝ) * x i)
    ring
  unfold fourierCharacter paperCharacter
  rw [hsum]
  change Complex.exp (((paperScale * (paperScale⁻¹ *
    ∑ i : Fin 3, (k i : ℝ) * x i) : ℝ) : ℂ) * Complex.I) = _
  rw [← mul_assoc, mul_inv_cancel₀ paperScale_pos.ne', one_mul]

def paperFiniteSynthesis (N : ℕ) (c : FourierCoeff) : Field :=
  fun x => WithLp.toLp 2 (fun i : Fin 3 =>
    (∑ k ∈ cutoffModes N, paperCharacter k x * c k i).re)

theorem dilatedFiniteSynthesis_eq_paper (N : ℕ) (c : FourierCoeff) :
    dilatedField paperScale (finiteSynthesis N c) = paperFiniteSynthesis N c := by
  funext x
  ext i
  change (∑ k ∈ cutoffModes N,
    fourierCharacter k (paperScale⁻¹ • x) * c k i).re = _
  simp only [fourierCharacter_dilated]
  rfl

end
end SingularClosure.H12Frontier
