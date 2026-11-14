import SingularClosure.CriticalHolder
import SingularClosure.CriticalSobolev

/-! The uniform critical nonlinear estimate for actual finite periodic fields.
The fractional embedding, physical Holder inequalities, and coefficient
interpolation are all proved dependencies, not hypotheses of the endpoint. -/

set_option autoImplicit false
set_option Elab.async true

noncomputable section

open Set MeasureTheory
open scoped ContDiff ENNReal NNReal BigOperators

namespace SingularClosure

theorem criticalEnergy_derivative_le (N : ℕ) (c : FourierCoeff) (i : Fin 3) :
    criticalEnergy 1 N (spectralMultiplier (derivativeSymbol i) c) ≤
      criticalEnergy 3 N c := by
  calc
    _ ≤ ∑ j : Fin 3, criticalEnergy 1 N (spectralMultiplier (derivativeSymbol j) c) :=
      Finset.single_le_sum
        (fun j _ => criticalEnergy_nonneg 1 N (spectralMultiplier (derivativeSymbol j) c))
        (Finset.mem_univ i)
    _ = _ := criticalEnergy_derivative_sum 1 N c

theorem FINITE_CRITICAL_DERIVATIVE_L3 :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ N : ℕ, ∀ c : FourierCoeff,
      eLpNorm (fderiv ℝ (finiteSynthesis N c)) 3 (volume.restrict unitCube) ≤
        C * (ENNReal.ofReal (criticalEnergy 3 N c)) ^ (1 / 2 : ℝ) := by
  obtain ⟨C, hC, hSob⟩ := FINITE_CRITICAL_HHALF_L3
  refine ⟨3 * C, by finiteness, ?_⟩
  intro N c
  apply finite_critical_derivative_L3_of_component_bound N c C
  intro i
  rw [finiteSynthesis_coordinateDerivative]
  exact (hSob N (spectralMultiplier (derivativeSymbol i) c)).trans
    (mul_le_mul_of_nonneg_left
      (ENNReal.rpow_le_rpow
        (ENNReal.ofReal_le_ofReal (criticalEnergy_derivative_le N c i))
        (by norm_num)) bot_le)

theorem ennreal_critical_holder_product (A B E Z : ℝ≥0∞) :
    ((A * E ^ (1 / 2 : ℝ)) * (B * Z ^ (1 / 2 : ℝ))) * E ^ (1 / 2 : ℝ) =
      (A * B) * E * Z ^ (1 / 2 : ℝ) := by
  calc
    _ = (A * B) * (E ^ (1 / 2 : ℝ) * E ^ (1 / 2 : ℝ)) *
        Z ^ (1 / 2 : ℝ) := by ring
    _ = _ := by
      rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
      norm_num

/-- The constant is chosen before the cutoff and every coefficient family.
Only the actual support, reality, and solenoidal constraints remain. -/
theorem FINITE_CRITICAL_NONLINEAR_BOUND :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∀ c : FourierCoeff,
      (∀ k : Frequency, k ∉ cutoffModes N → ∀ i : Fin 3, c k i = 0) →
      SpectralReality c → SpectralSolenoidal c →
      |criticalNonlinearPower 1 N c| ≤
        C * Real.sqrt (criticalEnergy 1 N c) * criticalEnergy 3 N c := by
  obtain ⟨A, hA, hSob⟩ := FINITE_PHYSICAL_L6_FROM_ENSTROPHY
  obtain ⟨B, hB, hDeriv⟩ := FINITE_CRITICAL_DERIVATIVE_L3
  let K : ℝ≥0∞ := A * B
  have hK : K < ⊤ := by dsimp [K]; finiteness
  refine ⟨K.toReal + 1, by positivity, ?_⟩
  intro N c hsupp hreal hsol
  have hE1 := criticalEnergy_nonneg 1 N c
  have hE2 := criticalEnergy_nonneg 2 N c
  have hE3 := criticalEnergy_nonneg 3 N c
  have hV6 : eLpNorm (finiteSynthesis N c) 6 (volume.restrict unitCube) ≤
      A * (ENNReal.ofReal (criticalEnergy 2 N c)) ^ (1 / 2 : ℝ) := by
    rw [criticalEnergy_two_eq_coefficientDissipation]
    exact hSob N c hreal
  have hD3 := hDeriv N c
  have hbound : ENNReal.ofReal (abs (criticalNonlinearPower 1 N c)) ≤
      K * ENNReal.ofReal (criticalEnergy 2 N c) *
        (ENNReal.ofReal (criticalEnergy 3 N c)) ^ (1 / 2 : ℝ) := by
    calc
      _ ≤ (eLpNorm (finiteSynthesis N c) 6 (volume.restrict unitCube) *
          eLpNorm (fderiv ℝ (finiteSynthesis N c)) 3 (volume.restrict unitCube)) *
          (ENNReal.ofReal (criticalEnergy 2 N c)) ^ (1 / 2 : ℝ) :=
        criticalNonlinearPower_one_enorm_le N c hsupp hreal hsol
      _ ≤ ((A * (ENNReal.ofReal (criticalEnergy 2 N c)) ^ (1 / 2 : ℝ)) *
          (B * (ENNReal.ofReal (criticalEnergy 3 N c)) ^ (1 / 2 : ℝ))) *
          (ENNReal.ofReal (criticalEnergy 2 N c)) ^ (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul hV6 hD3 bot_le bot_le) bot_le
      _ = _ := ennreal_critical_holder_product A B _ _
  have hr := ENNReal.toReal_mono (by finiteness) hbound
  simp only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal (abs_nonneg _), ENNReal.toReal_ofReal hE2,
    ENNReal.toReal_ofReal hE3, ← Real.sqrt_eq_rpow] at hr
  have hinterp := mul_le_mul_of_nonneg_right (criticalEnergy_interpolation_sqrt N c)
    (Real.sqrt_nonneg (criticalEnergy 3 N c))
  have hproduct : criticalEnergy 2 N c * Real.sqrt (criticalEnergy 3 N c) ≤
      Real.sqrt (criticalEnergy 1 N c) * criticalEnergy 3 N c := by
    calc
      _ ≤ (Real.sqrt (criticalEnergy 1 N c) * Real.sqrt (criticalEnergy 3 N c)) *
          Real.sqrt (criticalEnergy 3 N c) := hinterp
      _ = _ := by rw [mul_assoc, ← pow_two, Real.sq_sqrt hE3]
  calc
    _ ≤ K.toReal * criticalEnergy 2 N c * Real.sqrt (criticalEnergy 3 N c) := hr
    _ = K.toReal * (criticalEnergy 2 N c * Real.sqrt (criticalEnergy 3 N c)) := by ring
    _ ≤ K.toReal * (Real.sqrt (criticalEnergy 1 N c) * criticalEnergy 3 N c) :=
      mul_le_mul_of_nonneg_left hproduct ENNReal.toReal_nonneg
    _ ≤ (K.toReal + 1) * (Real.sqrt (criticalEnergy 1 N c) * criticalEnergy 3 N c) :=
      mul_le_mul_of_nonneg_right (by linarith)
        (mul_nonneg (Real.sqrt_nonneg _) hE3)
    _ = _ := by ring

end SingularClosure
