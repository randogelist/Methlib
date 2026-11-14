import SingularClosure.H12Frontier.Dilation

/-! Concrete admissible finite-Fourier Sobolev constants on the literal
2*pi cube. These are conservative proved constants, not optimal constants and
not an identification with the original repository's selected coefficient. -/
set_option autoImplicit false
set_option Elab.async true
open Set MeasureTheory
open scoped ENNReal NNReal BigOperators Pointwise
namespace SingularClosure.H12Frontier
noncomputable section

def paperFiniteEnergy (q N : ℕ) (c : FourierCoeff) : ℝ :=
  ∑ k ∈ cutoffModes N, ∑ i : Fin 3,
    paperFrequency k ^ q * Complex.normSq (c k i)

def paperFiniteNorm (q N : ℕ) (c : FourierCoeff) : ℝ :=
  Real.sqrt (paperFiniteEnergy q N c)

theorem paperFiniteEnergy_nonneg (q N : ℕ) (c : FourierCoeff) :
    0 ≤ paperFiniteEnergy q N c := by
  unfold paperFiniteEnergy
  exact Finset.sum_nonneg (fun k _ => Finset.sum_nonneg (fun i _ =>
    mul_nonneg (pow_nonneg (Real.sqrt_nonneg _) q) (Complex.normSq_nonneg _)))

theorem finiteEnergy_normalization (q N : ℕ) (c : FourierCoeff) :
    criticalEnergy q N c = paperScale ^ q * paperFiniteEnergy q N c := by
  unfold criticalEnergy paperFiniteEnergy
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hk0 : k ≠ 0 := ((mem_cutoffModes_iff N k).mp hk).2.1
  apply Finset.sum_congr rfl
  intro i _
  rw [criticalFrequencyWeight_eq_paper k hk0, mul_pow]
  unfold paperScale
  ring

theorem finiteNorm_normalization (q N : ℕ) (c : FourierCoeff) :
    Real.sqrt (criticalEnergy q N c) =
      Real.sqrt (paperScale ^ q) * paperFiniteNorm q N c := by
  rw [finiteEnergy_normalization,
    Real.sqrt_mul (pow_nonneg paperScale_pos.le q)]
  rfl

theorem finiteNorm_one (N : ℕ) (c : FourierCoeff) :
    Real.sqrt (criticalEnergy 1 N c) =
      Real.sqrt paperScale * paperFiniteNorm 1 N c := by
  simpa only [pow_one] using finiteNorm_normalization 1 N c

theorem finiteNorm_two (N : ℕ) (c : FourierCoeff) :
    Real.sqrt (criticalEnergy 2 N c) = paperScale * paperFiniteNorm 2 N c := by
  simpa only [Real.sqrt_sq paperScale_pos.le] using finiteNorm_normalization 2 N c

theorem finiteNorm_zero (N : ℕ) (c : FourierCoeff) :
    Real.sqrt (criticalEnergy 0 N c) = paperFiniteNorm 0 N c := by
  simpa only [pow_zero, Real.sqrt_one, one_mul] using finiteNorm_normalization 0 N c

theorem ofReal_sqrt_eq_rpow (x : ℝ) (hx : 0 ≤ x) :
    ENNReal.ofReal (Real.sqrt x) = (ENNReal.ofReal x) ^ (1 / 2 : ℝ) := by
  rw [Real.sqrt_eq_rpow, ENNReal.ofReal_rpow_of_nonneg hx (by norm_num)]

/-- Ordinary-volume L2 normalization on Q_(2*pi). -/
def CSZero : ℝ := paperScale * Real.sqrt paperScale

/-- A proved admissible H1 -> L6 coefficient on Q_(2*pi). -/
def CSOne : ℝ := Real.sqrt paperScale * (nativeSix * paperScale)

/-- A proved admissible Hhalf -> L3 coefficient on Q_(2*pi). -/
def CSHalf : ℝ := paperScale * (nativeThree * Real.sqrt paperScale)

theorem CSZero_pos : 0 < CSZero :=
  mul_pos paperScale_pos (Real.sqrt_pos.mpr paperScale_pos)

theorem CSOne_pos : 0 < CSOne :=
  mul_pos (Real.sqrt_pos.mpr paperScale_pos) (mul_pos nativeSix_pos paperScale_pos)

theorem CSHalf_pos : 0 < CSHalf :=
  mul_pos paperScale_pos (mul_pos nativeThree_pos (Real.sqrt_pos.mpr paperScale_pos))

theorem paperFinite_L3_bound (N : ℕ) (c : FourierCoeff) :
    eLpNorm (dilatedField paperScale (finiteSynthesis N c)) 3
        (volume.restrict (dilatedCube paperScale)) ≤
      ENNReal.ofReal CSHalf * ENNReal.ofReal (paperFiniteNorm 1 N c) := by
  rw [dilated_eLpNorm_three paperScale paperScale_pos _
    (finiteSynthesis_contDiff N c).continuous]
  calc
    _ ≤ ENNReal.ofReal paperScale * (ENNReal.ofReal nativeThree *
        (ENNReal.ofReal (criticalEnergy 1 N c)) ^ (1 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_left (nativeHalf_bound N c) bot_le
    _ = _ := by
      rw [← ofReal_sqrt_eq_rpow _ (criticalEnergy_nonneg 1 N c), finiteNorm_one]
      unfold CSHalf
      rw [ENNReal.ofReal_mul (Real.sqrt_nonneg paperScale),
        ENNReal.ofReal_mul paperScale_pos.le, ENNReal.ofReal_mul nativeThree_pos.le]
      ring

theorem paperFinite_L6_bound (N : ℕ) (c : FourierCoeff)
    (hr : SpectralReality c) :
    eLpNorm (dilatedField paperScale (finiteSynthesis N c)) 6
        (volume.restrict (dilatedCube paperScale)) ≤
      ENNReal.ofReal CSOne * ENNReal.ofReal (paperFiniteNorm 2 N c) := by
  rw [dilated_eLpNorm_six paperScale paperScale_pos _
    (finiteSynthesis_contDiff N c).continuous]
  have h := nativeSix_bound N c hr
  rw [← criticalEnergy_two_eq_coefficientDissipation] at h
  calc
    _ ≤ ENNReal.ofReal (Real.sqrt paperScale) * (ENNReal.ofReal nativeSix *
        (ENNReal.ofReal (criticalEnergy 2 N c)) ^ (1 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_left h bot_le
    _ = _ := by
      rw [← ofReal_sqrt_eq_rpow _ (criticalEnergy_nonneg 2 N c), finiteNorm_two]
      unfold CSOne
      rw [ENNReal.ofReal_mul paperScale_pos.le,
        ENNReal.ofReal_mul (Real.sqrt_nonneg paperScale),
        ENNReal.ofReal_mul nativeSix_pos.le]
      ring

theorem finite_L2_exact (N : ℕ) (c : FourierCoeff) (hr : SpectralReality c) :
    eLpNorm (finiteSynthesis N c) 2 (volume.restrict unitCube) =
      ENNReal.ofReal (Real.sqrt (criticalEnergy 0 N c)) := by
  have hi : IntegrableOn (fun x => ‖finiteSynthesis N c x‖ ^ 2) unitCube volume :=
    ((finiteSynthesis_contDiff N c).continuous.norm.pow 2).continuousOn.integrableOn_compact
      isCompact_unitCube
  rw [eLpNorm_two_eq_integral_norm_sq_rpow _ _ hi,
    ← physicalEnergy_eq_integral_norm_sq, FINITE_PHYSICAL_ENERGY_PARSEVAL N c hr]
  have he : criticalEnergy 0 N c = coefficientEnergy N c := by
    simp only [criticalEnergy, coefficientEnergy, pow_zero, one_mul]
  rw [← he, ofReal_sqrt_eq_rpow _ (criticalEnergy_nonneg 0 N c)]

theorem paperFinite_L2_exact (N : ℕ) (c : FourierCoeff)
    (hr : SpectralReality c) :
    eLpNorm (dilatedField paperScale (finiteSynthesis N c)) 2
        (volume.restrict (dilatedCube paperScale)) =
      ENNReal.ofReal CSZero * ENNReal.ofReal (paperFiniteNorm 0 N c) := by
  rw [dilated_eLpNorm_two paperScale paperScale_pos _
    (finiteSynthesis_contDiff N c).continuous, finite_L2_exact N c hr, finiteNorm_zero]
  rfl

/-- Fixed literal alpha=1/2, L=1 literature expression, with the above
actual admissible constants. No optimized or repository-equality claim. -/
def literatureK2 : ℝ :=
  Real.sqrt 2 * CSHalf * CSOne * CSZero / paperScale

def frontierConstant : ℝ := literatureK2 / (2 * Real.sqrt Real.pi)

theorem literatureK2_pos : 0 < literatureK2 := by
  unfold literatureK2
  exact div_pos (mul_pos (mul_pos (mul_pos (Real.sqrt_pos.mpr (by norm_num))
    CSHalf_pos) CSOne_pos) CSZero_pos) paperScale_pos

theorem frontierConstant_pos : 0 < frontierConstant :=
  div_pos literatureK2_pos (mul_pos (by norm_num) (Real.sqrt_pos.mpr Real.pi_pos))

theorem sqrt_scale_relation : Real.sqrt 2 * Real.sqrt paperScale =
    2 * Real.sqrt Real.pi := by
  apply (sq_eq_sq₀ (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))).mp
  simp only [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
    Real.sq_sqrt paperScale_pos.le, Real.sq_sqrt Real.pi_pos.le]
  unfold paperScale
  ring

theorem frontierConstant_eq_nativeProduct :
    frontierConstant = paperScale ^ 3 * nativeProduct := by
  unfold frontierConstant
  apply (div_eq_iff (ne_of_gt (mul_pos (by norm_num) (Real.sqrt_pos.mpr Real.pi_pos)))).mpr
  unfold literatureK2
  apply (div_eq_iff paperScale_pos.ne').mpr
  have hcube : Real.sqrt paperScale ^ 3 = paperScale * Real.sqrt paperScale := by
    rw [pow_succ, Real.sq_sqrt paperScale_pos.le]
  calc
    _ = Real.sqrt 2 * paperScale ^ 3 * nativeProduct * Real.sqrt paperScale ^ 3 := by
      unfold CSHalf CSOne CSZero nativeProduct
      ring
    _ = Real.sqrt 2 * paperScale ^ 3 * nativeProduct * (paperScale * Real.sqrt paperScale) := by
      rw [hcube]
    _ = _ := by rw [← sqrt_scale_relation]; ring

theorem nativeProduct_le_frontierConstant : nativeProduct ≤ frontierConstant := by
  rw [frontierConstant_eq_nativeProduct]
  have hs : (1 : ℝ) ≤ paperScale ^ 3 := one_le_pow₀ paperScale_one_le
  nlinarith [mul_le_mul_of_nonneg_right hs nativeProduct_pos.le]

/-- Every analytic input is a proved physical finite-polynomial estimate. -/
theorem CONCRETE_LITERATURE_SOBOLEV_BUNDLE :
    0 < CSZero ∧ 0 < CSHalf ∧ 0 < CSOne ∧
    (∀ N c, eLpNorm (dilatedField paperScale (finiteSynthesis N c)) 3
      (volume.restrict (dilatedCube paperScale)) ≤
        ENNReal.ofReal CSHalf * ENNReal.ofReal (paperFiniteNorm 1 N c)) ∧
    (∀ N c, SpectralReality c →
      eLpNorm (dilatedField paperScale (finiteSynthesis N c)) 6
        (volume.restrict (dilatedCube paperScale)) ≤
          ENNReal.ofReal CSOne * ENNReal.ofReal (paperFiniteNorm 2 N c)) ∧
    (∀ N c, SpectralReality c →
      eLpNorm (dilatedField paperScale (finiteSynthesis N c)) 2
        (volume.restrict (dilatedCube paperScale)) =
          ENNReal.ofReal CSZero * ENNReal.ofReal (paperFiniteNorm 0 N c)) :=
  ⟨CSZero_pos, CSHalf_pos, CSOne_pos, paperFinite_L3_bound,
    paperFinite_L6_bound, paperFinite_L2_exact⟩

end
end SingularClosure.H12Frontier
