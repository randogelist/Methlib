import SingularClosure.SobolevLimitBounds
import SingularClosure.SobolevSmoothRealization
import SingularClosure.SobolevTrajectoryCalculus

/-! Actual Fourier evaluation as a spatially differentiable operator-valued
map. Four spare Sobolev orders suffice for absolute operator-norm summability. -/

set_option autoImplicit false
set_option Elab.async true

open Set
open scoped BigOperators ContDiff

namespace SingularClosure

noncomputable section

section BanachSeries

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F] [CompleteSpace F]

def banachFourierSeries (A : Frequency → F) (x : Vec) : F :=
  ∑' k : Frequency, fourierCharacter k x • A k

theorem banachFourierSeries_summable (A : Frequency → F)
    (hA : Summable (fun k => ‖A k‖)) (x : Vec) :
    Summable (fun k : Frequency => fourierCharacter k x • A k) := by
  apply Summable.of_norm_bounded hA
  intro k
  simp only [norm_smul, fourierCharacter_norm, one_mul, le_refl]

theorem banachFourierSeries_continuous (A : Frequency → F)
    (hA : Summable (fun k => ‖A k‖)) : Continuous (banachFourierSeries A) :=
  continuous_tsum (fun k => (fourierCharacter_contDiff k).continuous.smul continuous_const)
    hA (fun k x => by simp only [norm_smul, fourierCharacter_norm, one_mul, le_refl])

theorem banachFourierSeries_derivative_bound (A : Frequency → F) (k : Frequency) (x : Vec) :
    ‖(fourierCharacter k x • fourierPhaseCLM k).smulRight (A k)‖ ≤
      ‖A k‖ * ‖fourierPhaseCLM k‖ := by
  apply ContinuousLinearMap.opNorm_le_bound (by positivity)
  intro y
  change ‖(fourierCharacter k x * fourierPhaseCLM k y) • A k‖ ≤ _
  rw [norm_smul, norm_mul, fourierCharacter_norm, one_mul]
  calc
    _ ≤ (‖fourierPhaseCLM k‖ * ‖y‖) * ‖A k‖ :=
      mul_le_mul_of_nonneg_right ((fourierPhaseCLM k).le_opNorm y) (norm_nonneg _)
    _ = _ := by ring

theorem banachFourierSeries_hasFDerivAt (A : Frequency → F)
    (hzero : Summable (fun k => ‖A k‖))
    (hone : Summable (fun k => ‖A k‖ * ‖fourierPhaseCLM k‖)) (x : Vec) :
    HasFDerivAt (banachFourierSeries A)
      (∑' k : Frequency, (fourierCharacter k x • fourierPhaseCLM k).smulRight (A k)) x :=
  hasFDerivAt_tsum hone
    (fun k y => (fourierCharacter_hasFDerivAt k y).smul_const (A k))
    (fun k y => banachFourierSeries_derivative_bound A k y)
    (banachFourierSeries_summable A hzero (0 : Vec)) x

theorem banachFourierSeries_fderiv_apply (A : Frequency → F)
    (hzero : Summable (fun k => ‖A k‖))
    (hone : Summable (fun k => ‖A k‖ * ‖fourierPhaseCLM k‖)) (x y : Vec) :
    fderiv ℝ (banachFourierSeries A) x y =
      banachFourierSeries (fun k => fourierPhaseCLM k y • A k) x := by
  rw [(banachFourierSeries_hasFDerivAt A hzero hone x).fderiv]
  have hs : Summable (fun k : Frequency =>
      (fourierCharacter k x • fourierPhaseCLM k).smulRight (A k)) :=
    Summable.of_norm_bounded hone (fun k => banachFourierSeries_derivative_bound A k x)
  have happ := (ContinuousLinearMap.apply ℝ F y).map_tsum hs
  calc
    _ = ∑' k : Frequency,
        ((fourierCharacter k x • fourierPhaseCLM k).smulRight (A k)) y := happ
    _ = _ := by
      apply tsum_congr
      intro k
      simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smul_apply,
        smul_eq_mul, mul_smul]

theorem banachFourierSeries_contDiff_nat (n : ℕ) (A : Frequency → F)
    (hA : ∀ m : ℕ, m ≤ n → Summable (fun k => ‖A k‖ * ‖fourierPhaseCLM k‖ ^ m)) :
    ContDiff ℝ n (banachFourierSeries A) := by
  induction n generalizing A with
  | zero =>
      have hzero : Summable (fun k => ‖A k‖) := by
        simpa only [pow_zero, mul_one] using hA 0 (Nat.zero_le 0)
      exact contDiff_zero.mpr (banachFourierSeries_continuous A hzero)
  | succ n ih =>
      have hzero : Summable (fun k => ‖A k‖) := by
        simpa only [pow_zero, mul_one] using hA 0 (Nat.zero_le (n + 1))
      have hone : Summable (fun k => ‖A k‖ * ‖fourierPhaseCLM k‖) := by
        simpa only [pow_one] using hA 1 (by omega)
      change ContDiff ℝ ((n : ℕ∞ω) + 1) (banachFourierSeries A)
      apply contDiff_succ_iff_fderiv_apply.mpr
      refine ⟨fun x => (banachFourierSeries_hasFDerivAt A hzero hone x).differentiableAt,
        by simp, ?_⟩
      intro y
      have heq : (fun x => fderiv ℝ (banachFourierSeries A) x y) =
          banachFourierSeries (fun k => fourierPhaseCLM k y • A k) := by
        funext x
        exact banachFourierSeries_fderiv_apply A hzero hone x y
      rw [heq]
      apply ih
      intro m hm
      apply Summable.of_nonneg_of_le
        (fun k => mul_nonneg (norm_nonneg _) (pow_nonneg (norm_nonneg _) _)) _
        ((hA (m + 1) (by omega)).mul_left ‖y‖)
      intro k
      rw [norm_smul]
      calc
        _ ≤ (‖fourierPhaseCLM k‖ * ‖y‖) * ‖A k‖ * ‖fourierPhaseCLM k‖ ^ m :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right ((fourierPhaseCLM k).le_opNorm y) (norm_nonneg _))
            (pow_nonneg (norm_nonneg _) _)
        _ = _ := by rw [pow_succ]; ring

end BanachSeries

theorem torusSobolevCoeff_norm_le_inv_weight (s : ℕ) (k : Frequency) (i : Fin 3) :
    ‖torusSobolevCoeff s k i‖ ≤ (torusSobolevWeight k ^ s)⁻¹ := by
  have hw : 0 ≤ (torusSobolevWeight k ^ s)⁻¹ := by positivity
  apply ContinuousLinearMap.opNorm_le_bound hw
  intro c
  calc
    ‖torusSobolevCoeff s k i c‖ =
        (torusSobolevWeight k ^ s)⁻¹ * ‖torusSobolevRepr s c (k, i)‖ := by
      change ‖((torusSobolevWeight k : ℂ) ^ s)⁻¹ *
        torusSobolevRepr s c (k, i)‖ = _
      rw [norm_mul, norm_inv, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (torusSobolevWeight_pos k)]
    _ ≤ (torusSobolevWeight k ^ s)⁻¹ * ‖torusSobolevRepr s c‖ :=
      mul_le_mul_of_nonneg_left
        (lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
          (torusSobolevRepr s c) (k, i)) hw
    _ = _ := by rw [(torusSobolevRepr s).norm_map]

theorem sobolevEvaluation_moment_summable (n m : ℕ) (hm : m ≤ n) (i : Fin 3) :
    Summable (fun k : Frequency =>
      ‖torusSobolevCoeff (n + 4) k i‖ * ‖fourierPhaseCLM k‖ ^ m) := by
  have hK := fourierPhaseWeightConstant_nonneg
  apply Summable.of_nonneg_of_le
    (fun k => mul_nonneg (norm_nonneg _) (pow_nonneg (norm_nonneg _) _)) _
    (summable_torusSobolevWeight_inv_four.mul_left (fourierPhaseWeightConstant ^ m))
  intro k
  have hw := (torusSobolevWeight_pos k).ne'
  have hpow : torusSobolevWeight k ^ m ≤ torusSobolevWeight k ^ n :=
    pow_le_pow_right₀ (torusSobolevWeight_one_le k) hm
  calc
    _ ≤ (torusSobolevWeight k ^ (n + 4))⁻¹ *
        (fourierPhaseWeightConstant * torusSobolevWeight k) ^ m :=
      mul_le_mul (torusSobolevCoeff_norm_le_inv_weight (n + 4) k i)
        (pow_le_pow_left₀ (norm_nonneg _) (fourierPhaseCLM_norm_le_weight k) m)
        (pow_nonneg (norm_nonneg _) _) (by positivity)
    _ = (fourierPhaseWeightConstant ^ m * (torusSobolevWeight k ^ (n + 4))⁻¹) *
        torusSobolevWeight k ^ m := by rw [mul_pow]; ring
    _ ≤ (fourierPhaseWeightConstant ^ m * (torusSobolevWeight k ^ (n + 4))⁻¹) *
        torusSobolevWeight k ^ n :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = _ := by rw [pow_add]; field_simp [hw] <;> ring

/-- The complex scalar evaluation operator. Its parameter n reserves n spatial
derivatives and four additional summability orders. -/
def sobolevScalarEvaluation (n : ℕ) (x : Vec) (i : Fin 3) :
    TorusSobolev (n + 4) →L[ℂ] ℂ :=
  banachFourierSeries (fun k => torusSobolevCoeff (n + 4) k i) x

theorem sobolevScalarEvaluation_summable (n : ℕ) (x : Vec) (i : Fin 3) :
    Summable (fun k : Frequency => fourierCharacter k x • torusSobolevCoeff (n + 4) k i) := by
  apply banachFourierSeries_summable
  simpa only [pow_zero, mul_one] using sobolevEvaluation_moment_summable n 0 (Nat.zero_le n) i

theorem sobolevScalarEvaluation_apply (n : ℕ) (x : Vec) (i : Fin 3)
    (c : TorusSobolev (n + 4)) :
    sobolevScalarEvaluation n x i c = scalarFourierSeries (fun k => c.val k i) x := by
  have h := (ContinuousLinearMap.apply ℂ ℂ c).map_tsum
    (sobolevScalarEvaluation_summable n x i)
  simpa only [sobolevScalarEvaluation, banachFourierSeries, scalarFourierSeries,
    ContinuousLinearMap.smul_apply, smul_eq_mul, torusSobolevCoeff_apply] using h

theorem sobolevScalarEvaluation_contDiff (n : ℕ) (i : Fin 3) :
    ContDiff ℝ n (fun x : Vec => sobolevScalarEvaluation n x i) :=
  banachFourierSeries_contDiff_nat n _ (fun m hm => sobolevEvaluation_moment_summable n m hm i)

theorem sobolevScalarEvaluation_real_contDiff (n : ℕ) (i : Fin 3) :
    ContDiff ℝ n (fun x : Vec => (sobolevScalarEvaluation n x i).restrictScalars ℝ) :=
  (ContinuousLinearMap.restrictScalarsL ℂ (TorusSobolev (n + 4)) ℂ ℝ ℝ).contDiff.comp
    (sobolevScalarEvaluation_contDiff n i)

/-- Real physical evaluation at a fixed point, in the actual vector codomain. -/
def sobolevPhysicalEvaluation (n : ℕ) (x : Vec) : TorusSobolev (n + 4) →L[ℝ] Vec :=
  ∑ i : Fin 3,
    (Complex.reCLM.comp ((sobolevScalarEvaluation n x i).restrictScalars ℝ)).smulRight (unitVector i)

theorem sobolevPhysicalEvaluation_apply (n : ℕ) (x : Vec) (c : TorusSobolev (n + 4)) :
    sobolevPhysicalEvaluation n x c = smoothFourierSynthesis c.val x := by
  ext j
  fin_cases j <;> simp [sobolevPhysicalEvaluation, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
    sobolevScalarEvaluation_apply, smoothFourierSynthesis, unitVector,
    Fin.sum_univ_succ, Pi.single_apply]

theorem sobolevPhysicalEvaluation_contDiff (n : ℕ) :
    ContDiff ℝ n (sobolevPhysicalEvaluation n) := by
  unfold sobolevPhysicalEvaluation
  apply ContDiff.sum
  intro i _
  exact (contDiff_const.clm_comp (sobolevScalarEvaluation_real_contDiff n i)).smulRight
    contDiff_const

abbrev sobolevScalarEvaluation4 (x : Vec) (i : Fin 3) : TorusSobolev 4 →L[ℂ] ℂ :=
  sobolevScalarEvaluation 0 x i

abbrev sobolevPhysicalEvaluation4 (x : Vec) : TorusSobolev 4 →L[ℝ] Vec :=
  sobolevPhysicalEvaluation 0 x

end

end SingularClosure
