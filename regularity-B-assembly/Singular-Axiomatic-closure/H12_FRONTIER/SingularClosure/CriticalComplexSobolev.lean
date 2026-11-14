import SingularClosure.PeriodicSobolev

/-!
Complex finite Fourier endpoint estimates for critical interpolation.
The coefficient functions need not satisfy conjugate reality: the scalar
complex-valued Sobolev theorem applies as a theorem over real scalars.
-/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

namespace SingularClosure
noncomputable section

theorem criticalComplex_contDiff (N : ℕ) (c : FourierCoeff) (j : Fin 3) :
    ContDiff ℝ ∞ (complexFiniteSynthesis N c j) :=
  ContDiff.sum fun k _ => (fourierCharacter_contDiff k).mul contDiff_const

theorem criticalComplex_periodic (N : ℕ) (c : FourierCoeff) (j : Fin 3) :
    SpatialPeriodic (complexFiniteSynthesis N c j) := by
  intro x i
  unfold complexFiniteSynthesis
  apply Finset.sum_congr rfl
  intro k _
  rw [fourierCharacter_periodic k x i]

theorem criticalComplex_coordinateDerivative (N : ℕ) (c : FourierCoeff)
    (j i : Fin 3) (x : Vec) :
    fderiv ℝ (complexFiniteSynthesis N c j) x (unitVector i) =
      complexFiniteSynthesis N (spectralMultiplier (derivativeSymbol i) c) j x := by
  have hs : HasFDerivAt (complexFiniteSynthesis N c j)
      (∑ k ∈ cutoffModes N,
        c k j • (fourierCharacter k x • fourierPhaseCLM k)) x :=
    HasFDerivAt.fun_sum fun k _ =>
      (fourierCharacter_hasFDerivAt k x).mul_const (c k j)
  rw [hs.fderiv]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, fourierPhaseCLM_unitVector, complexFiniteSynthesis,
    spectralMultiplier, mul_comm, mul_left_comm, mul_assoc]

theorem criticalComplex_integral_norm_sq (N : ℕ) (c : FourierCoeff) (j : Fin 3) :
    (∫ x in unitCube, ‖complexFiniteSynthesis N c j x‖ ^ 2) =
      ∑ k ∈ cutoffModes N, Complex.normSq (c k j) := by
  simpa only [Complex.normSq_eq_norm_sq] using
    integral_complexFiniteSynthesis_normSq N c j

theorem criticalComplex_componentEnergy_le (N : ℕ) (c : FourierCoeff) (j : Fin 3) :
    (∑ k ∈ cutoffModes N, Complex.normSq (c k j)) ≤ coefficientEnergy N c := by
  unfold coefficientEnergy
  apply Finset.sum_le_sum
  intro k _
  exact Finset.single_le_sum (fun i _ => Complex.normSq_nonneg (c k i))
    (Finset.mem_univ j)

theorem CRITICAL_COMPLEX_FINITE_L2 (N : ℕ) (c : FourierCoeff) (j : Fin 3) :
    eLpNorm (complexFiniteSynthesis N c j) 2 (volume.restrict unitCube) ≤
      (ENNReal.ofReal (coefficientEnergy N c)) ^ (1 / 2 : ℝ) := by
  have hi : IntegrableOn (fun x => ‖complexFiniteSynthesis N c j x‖ ^ 2)
      unitCube volume :=
    ((complexFiniteSynthesis_continuous N c j).norm.pow 2).continuousOn.integrableOn_compact
      isCompact_unitCube
  rw [eLpNorm_two_eq_integral_norm_sq_rpow _ _ hi,
    criticalComplex_integral_norm_sq]
  exact ENNReal.rpow_le_rpow
    (ENNReal.ofReal_le_ofReal (criticalComplex_componentEnergy_le N c j)) (by norm_num)

theorem criticalComplex_derivative_component_sum (N : ℕ) (c : FourierCoeff)
    (j : Fin 3) :
    (∑ i : Fin 3, ∑ k ∈ cutoffModes N,
      Complex.normSq (spectralMultiplier (derivativeSymbol i) c k j)) =
      ∑ k ∈ cutoffModes N,
        (2 * Real.pi) ^ 2 * (galerkinFreqSq k : ℝ) * Complex.normSq (c k j) := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  simp_rw [normSq_derivativeMultiplier]
  unfold galerkinFreqSq
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem criticalComplex_componentDissipation_le (N : ℕ) (c : FourierCoeff)
    (j : Fin 3) :
    (∑ k ∈ cutoffModes N,
      (2 * Real.pi) ^ 2 * (galerkinFreqSq k : ℝ) * Complex.normSq (c k j)) ≤
      coefficientDissipation N c := by
  unfold coefficientDissipation
  apply Finset.sum_le_sum
  intro k _
  have hk : (0 : ℝ) ≤ (galerkinFreqSq k : ℝ) := by
    have hkZ : (0 : ℤ) ≤ galerkinFreqSq k := by
      unfold galerkinFreqSq
      exact Finset.sum_nonneg (fun i _ => sq_nonneg (k i))
    exact_mod_cast hkZ
  exact Finset.single_le_sum (fun i _ =>
    mul_nonneg (mul_nonneg (sq_nonneg _) hk) (Complex.normSq_nonneg _))
      (Finset.mem_univ j)

theorem criticalComplex_fderiv_integral_le (N : ℕ) (c : FourierCoeff) (j : Fin 3) :
    (∫ x in unitCube, ‖fderiv ℝ (complexFiniteSynthesis N c j) x‖ ^ 2) ≤
      3 * coefficientDissipation N c := by
  let v := complexFiniteSynthesis N c j
  have hv : ContDiff ℝ ∞ v := criticalComplex_contDiff N c j
  have hd : Continuous (fderiv ℝ v) :=
    (hv.fderiv_right (m := 0) (by norm_num)).continuous
  have hi : IntegrableOn (fun x => ‖fderiv ℝ v x‖ ^ 2) unitCube volume :=
    (hd.norm.pow 2).continuousOn.integrableOn_compact isCompact_unitCube
  have hdi (i : Fin 3) : IntegrableOn
      (fun x => ‖complexFiniteSynthesis N (spectralMultiplier (derivativeSymbol i) c) j x‖ ^ 2)
      unitCube volume :=
    ((complexFiniteSynthesis_continuous N _ j).norm.pow 2).continuousOn.integrableOn_compact
      isCompact_unitCube
  have hpoint (x : Vec) : ‖fderiv ℝ v x‖ ^ 2 ≤
      3 * ∑ i : Fin 3,
        ‖complexFiniteSynthesis N (spectralMultiplier (derivativeSymbol i) c) j x‖ ^ 2 := by
    simpa only [v, criticalComplex_coordinateDerivative] using
      opNorm_sq_le_three_sum_coordinate_sq (fderiv ℝ v x)
  calc
    _ ≤ ∫ x in unitCube, 3 * ∑ i : Fin 3,
        ‖complexFiniteSynthesis N (spectralMultiplier (derivativeSymbol i) c) j x‖ ^ 2 :=
      integral_mono hi ((integrable_finset_sum _ (fun i _ => hdi i)).const_mul 3) hpoint
    _ = 3 * ∑ i : Fin 3, ∑ k ∈ cutoffModes N,
        Complex.normSq (spectralMultiplier (derivativeSymbol i) c k j) := by
      rw [integral_const_mul, integral_finsetSum Finset.univ (fun i _ => hdi i)]
      simp_rw [criticalComplex_integral_norm_sq]
    _ ≤ 3 * coefficientDissipation N c := by
      rw [criticalComplex_derivative_component_sum]
      exact mul_le_mul_of_nonneg_left (criticalComplex_componentDissipation_le N c j)
        (by norm_num)

theorem CRITICAL_COMPLEX_FINITE_L6 :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (N : ℕ) (c : FourierCoeff) (j : Fin 3),
      eLpNorm (complexFiniteSynthesis N c j) 6 (volume.restrict unitCube) ≤
        C * (ENNReal.ofReal (coefficientDissipation N c)) ^ (1 / 2 : ℝ) := by
  obtain ⟨K, hK0, hK⟩ := PERIODIC_SOBOLEV_H1_L6 (F := ℂ)
  let C : ℝ≥0∞ :=
    (SNormLESNormFDerivOfEqConst ℂ (volume : Measure Vec) 2 : ℝ≥0∞) *
      (343 : ℝ≥0∞) ^ (1 / 2 : ℝ) *
        ((3 : ℝ≥0∞) ^ (1 / 2 : ℝ) + ENNReal.ofReal K)
  refine ⟨C, ?_, ?_⟩
  · dsimp [C]
    finiteness
  intro N c j
  have hv := criticalComplex_contDiff N c j
  have hd : Continuous (fderiv ℝ (complexFiniteSynthesis N c j)) :=
    (hv.fderiv_right (m := 0) (by norm_num)).continuous
  have hi : IntegrableOn
      (fun x => ‖fderiv ℝ (complexFiniteSynthesis N c j) x‖ ^ 2) unitCube volume :=
    (hd.norm.pow 2).continuousOn.integrableOn_compact isCompact_unitCube
  have hD : eLpNorm (fderiv ℝ (complexFiniteSynthesis N c j)) 2
      (volume.restrict unitCube) ≤ (3 : ℝ≥0∞) ^ (1 / 2 : ℝ) *
        (ENNReal.ofReal (coefficientDissipation N c)) ^ (1 / 2 : ℝ) := by
    rw [eLpNorm_two_eq_integral_norm_sq_rpow _ _ hi]
    calc
      _ ≤ (ENNReal.ofReal (3 * coefficientDissipation N c)) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow
          (ENNReal.ofReal_le_ofReal (criticalComplex_fderiv_integral_le N c j)) (by norm_num)
      _ = _ := by
        rw [ENNReal.ofReal_mul (by norm_num),
          ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
        norm_num
  have hV : eLpNorm (complexFiniteSynthesis N c j) 2 (volume.restrict unitCube) ≤
      (ENNReal.ofReal (coefficientDissipation N c)) ^ (1 / 2 : ℝ) :=
    (CRITICAL_COMPLEX_FINITE_L2 N c j).trans (ENNReal.rpow_le_rpow
      (ENNReal.ofReal_le_ofReal (coefficientEnergy_le_dissipation N c)) (by norm_num))
  calc
    _ ≤ _ := hK (complexFiniteSynthesis N c j) hv (criticalComplex_periodic N c j)
    _ ≤ (SNormLESNormFDerivOfEqConst ℂ (volume : Measure Vec) 2 : ℝ≥0∞) *
        (343 : ℝ≥0∞) ^ (1 / 2 : ℝ) *
        ((3 : ℝ≥0∞) ^ (1 / 2 : ℝ) *
          (ENNReal.ofReal (coefficientDissipation N c)) ^ (1 / 2 : ℝ) +
          ENNReal.ofReal K *
            (ENNReal.ofReal (coefficientDissipation N c)) ^ (1 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_left
        (add_le_add hD (mul_le_mul_of_nonneg_left hV bot_le)) bot_le
    _ = _ := by dsimp [C]; ring

end
end SingularClosure
