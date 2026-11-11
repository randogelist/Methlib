import SingularClosure.EnstrophyAbsorption

/-!
# A universal physical L2 convection estimate

The constants are independent of the finite Fourier cutoff and the field.
This module supplies the nonlinear part of the actual time-derivative bound.
-/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory
open scoped ContDiff ENNReal NNReal BigOperators

namespace SingularClosure

noncomputable section

theorem ennreal_convection_product (A B E Z : ℝ≥0∞) :
    (A * E ^ (1 / 2 : ℝ)) *
        (((3 : ℝ≥0∞) ^ (1 / 2 : ℝ) * E ^ (1 / 2 : ℝ)) ^ (1 / 2 : ℝ) *
          (B * Z ^ (1 / 2 : ℝ)) ^ (1 / 2 : ℝ)) =
      (A * (3 : ℝ≥0∞) ^ (1 / 4 : ℝ) * B ^ (1 / 2 : ℝ)) *
        E ^ (3 / 4 : ℝ) * Z ^ (1 / 4 : ℝ) := by
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  simp only [← ENNReal.rpow_mul]
  norm_num
  calc
    _ = (A * (3 : ℝ≥0∞) ^ (1 / 4 : ℝ) * B ^ (1 / 2 : ℝ)) *
        (E ^ (1 / 2 : ℝ) * E ^ (1 / 4 : ℝ)) * Z ^ (1 / 4 : ℝ) := by ring
    _ = _ := by
      rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
      norm_num

theorem FINITE_CONVECTION_L2_BOUND :
    ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ N : ℕ, ∀ c : FourierCoeff, SpectralReality c →
      eLpNorm (convection (finiteSynthesis N c)) 2 (volume.restrict unitCube) ≤
        K * (ENNReal.ofReal (coefficientDissipation N c)) ^ (3 / 4 : ℝ) *
          (ENNReal.ofReal (coefficientLaplacianSquare N c)) ^ (1 / 4 : ℝ) := by
  obtain ⟨A, hA, hSob⟩ := FINITE_PHYSICAL_L6_FROM_ENSTROPHY
  obtain ⟨B, hB, hDeriv⟩ := FINITE_PHYSICAL_DERIVATIVE_L6_FROM_LAPLACIAN
  refine ⟨A * (3 : ℝ≥0∞) ^ (1 / 4 : ℝ) * B ^ (1 / 2 : ℝ),
    by finiteness, ?_⟩
  intro N c hreal
  have hv := finiteSynthesis_contDiff N c
  have hd : Continuous (fderiv ℝ (finiteSynthesis N c)) :=
    (hv.fderiv_right (m := 0) (by norm_num)).continuous
  have hD3 := cube_eLpNorm_three_le_interpolation (fderiv ℝ (finiteSynthesis N c)) hd
  have hD2 := finite_fderiv_eLpNorm_two_le N c hreal
  have hD6 := hDeriv N c hreal
  have hV6 := hSob N c hreal
  calc
    _ ≤ eLpNorm (finiteSynthesis N c) 6 (volume.restrict unitCube) *
        eLpNorm (fderiv ℝ (finiteSynthesis N c)) 3 (volume.restrict unitCube) :=
      convection_eLpNorm_two_le _ hv
    _ ≤ (A * (ENNReal.ofReal (coefficientDissipation N c)) ^ (1 / 2 : ℝ)) *
        (((3 : ℝ≥0∞) ^ (1 / 2 : ℝ) *
            (ENNReal.ofReal (coefficientDissipation N c)) ^ (1 / 2 : ℝ)) ^ (1 / 2 : ℝ) *
          (B * (ENNReal.ofReal (coefficientLaplacianSquare N c)) ^ (1 / 2 : ℝ)) ^
            (1 / 2 : ℝ)) := by
      refine mul_le_mul hV6 ?_ bot_le bot_le
      exact hD3.trans (mul_le_mul
        (ENNReal.rpow_le_rpow hD2 (by norm_num))
        (ENNReal.rpow_le_rpow hD6 (by norm_num)) bot_le bot_le)
    _ = _ := ennreal_convection_product _ _ _ _

theorem FINITE_CONVECTION_SQUARE_SHARP_BOUND :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, ∀ c : FourierCoeff, SpectralReality c →
      (∫ x in unitCube, ‖convection (finiteSynthesis N c) x‖ ^ 2) ≤
        C * (coefficientDissipation N c) ^ (3 / 2 : ℝ) *
          (coefficientLaplacianSquare N c) ^ (1 / 2 : ℝ) := by
  obtain ⟨K, hK, hbound⟩ := FINITE_CONVECTION_L2_BOUND
  refine ⟨K.toReal ^ 2, sq_nonneg _, ?_⟩
  intro N c hreal
  have hE := coefficientDissipation_nonneg N c
  have hZ := coefficientLaplacianSquare_nonneg N c
  have hcont := convection_continuous (finiteSynthesis_contDiff N c)
  have hi : IntegrableOn (fun x => ‖convection (finiteSynthesis N c) x‖ ^ 2)
      unitCube volume :=
    (hcont.norm.pow 2).continuousOn.integrableOn_compact isCompact_unitCube
  have hI : 0 ≤ ∫ x in unitCube, ‖convection (finiteSynthesis N c) x‖ ^ 2 :=
    integral_nonneg (fun x => sq_nonneg _)
  have h := hbound N c hreal
  rw [eLpNorm_two_eq_integral_norm_sq_rpow _ _ hi] at h
  have hr := ENNReal.toReal_mono (by finiteness) h
  simp only [ENNReal.toReal_mul, ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal hI, ENNReal.toReal_ofReal hE,
    ENNReal.toReal_ofReal hZ] at hr
  have hs := pow_le_pow_left₀ (Real.rpow_nonneg hI (1 / 2 : ℝ)) hr 2
  have hIeq : ((∫ x in unitCube, ‖convection (finiteSynthesis N c) x‖ ^ 2) ^
      (1 / 2 : ℝ)) ^ (2 : ℕ) = ∫ x in unitCube, ‖convection (finiteSynthesis N c) x‖ ^ 2 := by
    rw [← Real.rpow_mul_natCast hI]
    norm_num
  have hEeq : ((coefficientDissipation N c) ^ (3 / 4 : ℝ)) ^ (2 : ℕ) =
      (coefficientDissipation N c) ^ (3 / 2 : ℝ) := by
    rw [← Real.rpow_mul_natCast hE]
    norm_num
  have hZeq : ((coefficientLaplacianSquare N c) ^ (1 / 4 : ℝ)) ^ (2 : ℕ) =
      (coefficientLaplacianSquare N c) ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_mul_natCast hZ]
    norm_num
  rw [hIeq, mul_pow, mul_pow, hEeq, hZeq] at hs
  exact hs

theorem real_three_halves_mul_half_le (E Z : ℝ) (hE : 0 ≤ E) (hZ : 0 ≤ Z) :
    E ^ (3 / 2 : ℝ) * Z ^ (1 / 2 : ℝ) ≤ E ^ (3 : ℕ) + Z := by
  have hEeq : (E ^ (3 / 2 : ℝ)) ^ (2 : ℕ) = E ^ (3 : ℕ) := by
    rw [← Real.rpow_mul_natCast hE]
    norm_num
  have hZeq : (Z ^ (1 / 2 : ℝ)) ^ (2 : ℕ) = Z := by
    rw [← Real.rpow_mul_natCast hZ]
    norm_num
  nlinarith [sq_nonneg (E ^ (3 / 2 : ℝ) - Z ^ (1 / 2 : ℝ)), pow_nonneg hE 3]

theorem FINITE_CONVECTION_SQUARE_BOUND :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∀ c : FourierCoeff, SpectralReality c →
      (∫ x in unitCube, ‖convection (finiteSynthesis N c) x‖ ^ 2) ≤
        C * ((coefficientDissipation N c) ^ 3 + coefficientLaplacianSquare N c) := by
  obtain ⟨K, hK, hbound⟩ := FINITE_CONVECTION_SQUARE_SHARP_BOUND
  refine ⟨K + 1, by positivity, ?_⟩
  intro N c hreal
  have hE := coefficientDissipation_nonneg N c
  have hZ := coefficientLaplacianSquare_nonneg N c
  calc
    _ ≤ K * (coefficientDissipation N c) ^ (3 / 2 : ℝ) *
        (coefficientLaplacianSquare N c) ^ (1 / 2 : ℝ) := hbound N c hreal
    _ = K * ((coefficientDissipation N c) ^ (3 / 2 : ℝ) *
        (coefficientLaplacianSquare N c) ^ (1 / 2 : ℝ)) := by ring
    _ ≤ K * ((coefficientDissipation N c) ^ 3 + coefficientLaplacianSquare N c) :=
      mul_le_mul_of_nonneg_left (real_three_halves_mul_half_le _ _ hE hZ) hK
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith)
      (add_nonneg (pow_nonneg hE _) hZ)

/-- The convection bound stated entirely using actual physical integrals. -/
theorem FINITE_PHYSICAL_CONVECTION_SQUARE_BOUND :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∀ c : FourierCoeff, SpectralReality c →
      (∫ x in unitCube, ‖convection (finiteSynthesis N c) x‖ ^ 2) ≤
        C * ((∫ x in unitCube, gradientSquareDensity (finiteSynthesis N c) x) ^ 3 +
          ∫ x in unitCube, ‖laplacian (finiteSynthesis N c) x‖ ^ 2) := by
  obtain ⟨C, hC, hbound⟩ := FINITE_CONVECTION_SQUARE_BOUND
  refine ⟨C, hC, ?_⟩
  intro N c hreal
  rw [FINITE_PHYSICAL_REAL_ENSTROPHY_PARSEVAL N c hreal,
    finite_laplacian_integral_norm_sq N c hreal]
  exact hbound N c hreal

end

end SingularClosure
