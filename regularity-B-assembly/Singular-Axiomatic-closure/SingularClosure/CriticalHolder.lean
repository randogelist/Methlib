import SingularClosure.CriticalEnergy
import SingularClosure.PeriodicNonlinear

/-! Physical Holder estimates for the finite critical nonlinear pairing.
All fields are the actual finite Fourier synthesis and its derivatives. -/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

namespace SingularClosure

noncomputable section

theorem finite_criticalLambda_eLpNorm_two (N : ℕ) (c : FourierCoeff)
    (hreal : SpectralReality c) :
    eLpNorm (finiteSynthesis N (criticalLambdaCoefficient c)) 2
        (volume.restrict unitCube) =
      (ENNReal.ofReal (criticalEnergy 2 N c)) ^ (1 / 2 : ℝ) := by
  have hcont : Continuous
      (fun x => ‖finiteSynthesis N (criticalLambdaCoefficient c) x‖ ^ 2) :=
    (finiteSynthesis_contDiff N (criticalLambdaCoefficient c)).continuous.norm.pow 2
  have hi : IntegrableOn
      (fun x => ‖finiteSynthesis N (criticalLambdaCoefficient c) x‖ ^ 2)
      unitCube volume :=
    hcont.continuousOn.integrableOn_compact isCompact_unitCube
  rw [eLpNorm_two_eq_integral_norm_sq_rpow _ _ hi,
    FINITE_CRITICAL_LAMBDA_PARSEVAL N c hreal]

theorem criticalNonlinearPower_one_enorm_le
    (N : ℕ) (c : FourierCoeff)
    (hsupp : ∀ k : Frequency, k ∉ cutoffModes N → ∀ i : Fin 3, c k i = 0)
    (hreal : SpectralReality c) (hsol : SpectralSolenoidal c) :
    ENNReal.ofReal (abs (criticalNonlinearPower 1 N c)) ≤
      (eLpNorm (finiteSynthesis N c) 6 (volume.restrict unitCube) *
        eLpNorm (fderiv ℝ (finiteSynthesis N c)) 3 (volume.restrict unitCube)) *
          (ENNReal.ofReal (criticalEnergy 2 N c)) ^ (1 / 2 : ℝ) := by
  have hu := finiteSynthesis_contDiff N c
  rw [criticalNonlinearPower_one_eq_physical N c hsupp hreal hsol]
  calc
    _ ≤ eLpNorm (convection (finiteSynthesis N c)) 2 (volume.restrict unitCube) *
        eLpNorm (finiteSynthesis N (criticalLambdaCoefficient c)) 2
          (volume.restrict unitCube) :=
      inner_integral_enorm_le_eLpNorm_two _ _ (convection_continuous hu)
        (finiteSynthesis_contDiff N (criticalLambdaCoefficient c)).continuous
    _ ≤ _ := by
      rw [finite_criticalLambda_eLpNorm_two N c hreal]
      exact mul_le_mul_of_nonneg_right (convection_eLpNorm_two_le _ hu) bot_le

/-- Coordinate L3 bounds control the actual Frechet derivative operator norm. -/
theorem finite_critical_derivative_L3_of_component_bound
    (N : ℕ) (c : FourierCoeff) (C : ℝ≥0∞)
    (hcoord : ∀ i : Fin 3,
      eLpNorm (coordinateDerivative (finiteSynthesis N c) i) 3
          (volume.restrict unitCube) ≤
        C * (ENNReal.ofReal (criticalEnergy 3 N c)) ^ (1 / 2 : ℝ)) :
    eLpNorm (fderiv ℝ (finiteSynthesis N c)) 3 (volume.restrict unitCube) ≤
      (3 * C) * (ENNReal.ofReal (criticalEnergy 3 N c)) ^ (1 / 2 : ℝ) := by
  have hmeas (i : Fin 3) : AEStronglyMeasurable
      (fun x => ‖coordinateDerivative (finiteSynthesis N c) i x‖)
      (volume.restrict unitCube) := by
    rw [finiteSynthesis_coordinateDerivative]
    exact (finiteSynthesis_contDiff N _).continuous.norm.aestronglyMeasurable
  calc
    _ ≤ eLpNorm (fun x => ∑ i : Fin 3,
        ‖coordinateDerivative (finiteSynthesis N c) i x‖) 3 (volume.restrict unitCube) :=
      eLpNorm_mono_real (fun x => opNorm_le_sum_coordinate_norm (fderiv ℝ _ x))
    _ ≤ ∑ i : Fin 3,
        eLpNorm (fun x => ‖coordinateDerivative (finiteSynthesis N c) i x‖) 3
          (volume.restrict unitCube) := by
      have hsum : (fun x => ∑ i : Fin 3,
          ‖coordinateDerivative (finiteSynthesis N c) i x‖) =
          ∑ i : Fin 3, (fun x => ‖coordinateDerivative (finiteSynthesis N c) i x‖) := by
        funext x
        simp only [Finset.sum_apply]
      rw [hsum]
      exact eLpNorm_sum_le (s := Finset.univ) (fun i _ => hmeas i)
        (by norm_num : (1 : ℝ≥0∞) ≤ 3)
    _ = ∑ i : Fin 3,
        eLpNorm (coordinateDerivative (finiteSynthesis N c) i) 3
          (volume.restrict unitCube) := by simp only [eLpNorm_norm]
    _ ≤ ∑ _i : Fin 3,
        C * (ENNReal.ofReal (criticalEnergy 3 N c)) ^ (1 / 2 : ℝ) :=
      Finset.sum_le_sum (fun i _ => hcoord i)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      <;> ring

end

end SingularClosure
