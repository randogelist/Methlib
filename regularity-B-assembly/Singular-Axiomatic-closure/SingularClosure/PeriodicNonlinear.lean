import SingularClosure.PeriodicSobolev
import SingularClosure.FiniteHessian

/-!
# The actual finite periodic convection estimate

The constants in this module precede every cutoff and every coefficient
family. The proof uses the proved periodic Sobolev inequality, the actual
Hessian/Laplacian identity, Hölder interpolation and the actual convection
operator. No nonlinear estimate is supplied as an unresolved premise.
-/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory
open scoped ContDiff ENNReal NNReal BigOperators RealInnerProductSpace

namespace SingularClosure

noncomputable section

theorem coefficientEnergy_laplacianCoefficient (N : ℕ) (c : FourierCoeff) :
    coefficientEnergy N (laplacianCoefficient c) = coefficientLaplacianSquare N c := by
  simp only [coefficientEnergy, laplacianCoefficient, Complex.normSq_mul,
    Complex.normSq_neg, Complex.normSq_ofReal, coefficientLaplacianSquare,
    laplacianFrequency, pow_two]

theorem coefficientDissipation_derivative_le_laplacian (N : ℕ) (c : FourierCoeff)
    (i : Fin 3) :
    coefficientDissipation N (spectralMultiplier (derivativeSymbol i) c) ≤
      coefficientLaplacianSquare N c := by
  calc
    _ ≤ ∑ j : Fin 3,
        coefficientDissipation N (spectralMultiplier (derivativeSymbol j) c) :=
      Finset.single_le_sum (fun j _ => coefficientDissipation_nonneg N _) (Finset.mem_univ i)
    _ = _ := by
      rw [coefficientDissipation_derivative_sum, coefficientEnergy_laplacianCoefficient]

theorem finite_laplacian_eLpNorm_two (N : ℕ) (c : FourierCoeff)
    (hreal : SpectralReality c) :
    eLpNorm (laplacian (finiteSynthesis N c)) 2 (volume.restrict unitCube) =
      (ENNReal.ofReal (coefficientLaplacianSquare N c)) ^ (1 / 2 : ℝ) := by
  rw [finiteSynthesis_laplacian]
  have hc : Continuous (fun x => ‖finiteSynthesis N (laplacianCoefficient c) x‖ ^ 2) :=
    (finiteSynthesis_contDiff N (laplacianCoefficient c)).continuous.norm.pow 2
  have hi : IntegrableOn
      (fun x => ‖finiteSynthesis N (laplacianCoefficient c) x‖ ^ 2) unitCube volume :=
    hc.continuousOn.integrableOn_compact isCompact_unitCube
  rw [eLpNorm_two_eq_integral_norm_sq_rpow _ _ hi,
    ← physicalEnergy_eq_integral_norm_sq,
    FINITE_PHYSICAL_ENERGY_PARSEVAL N _ (laplacianCoefficient_reality c hreal),
    coefficientEnergy_laplacianCoefficient]

/-- A fixed L6 bound for the actual Fréchet derivative. -/
theorem FINITE_PHYSICAL_DERIVATIVE_L6_FROM_LAPLACIAN :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ N : ℕ, ∀ c : FourierCoeff, SpectralReality c →
      eLpNorm (fderiv ℝ (finiteSynthesis N c)) 6 (volume.restrict unitCube) ≤
        C * (ENNReal.ofReal (coefficientLaplacianSquare N c)) ^ (1 / 2 : ℝ) := by
  obtain ⟨C, hC, hSob⟩ := FINITE_PHYSICAL_L6_FROM_ENSTROPHY
  refine ⟨3 * C, by finiteness, ?_⟩
  intro N c hreal
  have hcoord (i : Fin 3) :
      eLpNorm (coordinateDerivative (finiteSynthesis N c) i) 6
          (volume.restrict unitCube) ≤
        C * (ENNReal.ofReal (coefficientLaplacianSquare N c)) ^ (1 / 2 : ℝ) := by
    rw [finiteSynthesis_coordinateDerivative]
    exact (hSob N _ (derivativeMultiplier_reality c hreal i)).trans
      (mul_le_mul_of_nonneg_left (ENNReal.rpow_le_rpow
        (ENNReal.ofReal_le_ofReal (coefficientDissipation_derivative_le_laplacian N c i))
        (by norm_num)) bot_le)
  have hmeas (i : Fin 3) : AEStronglyMeasurable
      (fun x => ‖coordinateDerivative (finiteSynthesis N c) i x‖)
      (volume.restrict unitCube) := by
    rw [finiteSynthesis_coordinateDerivative]
    exact (finiteSynthesis_contDiff N _).continuous.norm.aestronglyMeasurable
  calc
    _ ≤ eLpNorm (fun x => ∑ i : Fin 3,
        ‖coordinateDerivative (finiteSynthesis N c) i x‖) 6 (volume.restrict unitCube) :=
      eLpNorm_mono_real (fun x => opNorm_le_sum_coordinate_norm (fderiv ℝ _ x))
    _ ≤ ∑ i : Fin 3,
        eLpNorm (fun x => ‖coordinateDerivative (finiteSynthesis N c) i x‖) 6
          (volume.restrict unitCube) := by
      have hsum : (fun x => ∑ i : Fin 3,
          ‖coordinateDerivative (finiteSynthesis N c) i x‖) =
          ∑ i : Fin 3, (fun x => ‖coordinateDerivative (finiteSynthesis N c) i x‖) := by
        funext x
        simp only [Finset.sum_apply]
      rw [hsum]
      exact eLpNorm_sum_le (s := Finset.univ) (fun i _ => hmeas i)
        (by norm_num : (1 : ℝ≥0∞) ≤ 6)
    _ = ∑ i : Fin 3,
        eLpNorm (coordinateDerivative (finiteSynthesis N c) i) 6
          (volume.restrict unitCube) := by simp only [eLpNorm_norm]
    _ ≤ ∑ _i : Fin 3,
        C * (ENNReal.ofReal (coefficientLaplacianSquare N c)) ^ (1 / 2 : ℝ) :=
      Finset.sum_le_sum (fun i _ => hcoord i)
    _ = _ := by simp; ring

variable {F : Type*} [NormedAddCommGroup F]

/-- The concrete L2/L6 interpolation inequality on the physical cube. -/
theorem cube_eLpNorm_three_le_interpolation (v : Vec → F) (hv : Continuous v) :
    eLpNorm v 3 (volume.restrict unitCube) ≤
      eLpNorm v 2 (volume.restrict unitCube) ^ (1 / 2 : ℝ) *
        eLpNorm v 6 (volume.restrict unitCube) ^ (1 / 2 : ℝ) := by
  letI : ENNReal.HolderTriple 4 12 3 := by
    have h : Real.HolderTriple (4 : ℝ) 12 3 := by constructor <;> norm_num
    simpa using h.ennrealOfReal
  have hc : Continuous (fun x => ‖v x‖ ^ (1 / 2 : ℝ)) :=
    (Real.continuous_rpow_const (by norm_num)).comp hv.norm
  have hprod : (fun x => ‖v x‖ ^ (1 / 2 : ℝ) * ‖v x‖ ^ (1 / 2 : ℝ)) =
      (fun x => ‖v x‖) := by
    funext x
    rw [← Real.rpow_add_of_nonneg (norm_nonneg _) (by norm_num) (by norm_num)]
    norm_num
  have h := eLpNorm_le_eLpNorm_mul_eLpNorm'_of_norm
    (μ := volume.restrict unitCube) (p := 4) (q := 12) (r := 3)
    hc.aestronglyMeasurable hc.aestronglyMeasurable
    (fun a b : ℝ => a * b) 1
    (Filter.Eventually.of_forall (fun x => by
      simp only [norm_mul, NNReal.coe_one, one_mul, le_refl]))
  rw [hprod, eLpNorm_norm,
    eLpNorm_norm_rpow v (by norm_num), eLpNorm_norm_rpow v (by norm_num)] at h
  have h4 : (4 : ℝ≥0∞) * ENNReal.ofReal (1 / 2 : ℝ) = 2 := by
    calc
      _ = ENNReal.ofReal ((4 : ℝ) * (1 / 2 : ℝ)) := by
        rw [ENNReal.ofReal_mul (by norm_num)]
        norm_num
      _ = 2 := by norm_num
  have h12 : (12 : ℝ≥0∞) * ENNReal.ofReal (1 / 2 : ℝ) = 6 := by
    calc
      _ = ENNReal.ofReal ((12 : ℝ) * (1 / 2 : ℝ)) := by
        rw [ENNReal.ofReal_mul (by norm_num)]
        norm_num
      _ = 6 := by norm_num
  simpa only [h4, h12, ENNReal.coe_one, one_mul] using h

/-- Hölder for the actual derivative-evaluation definition of convection. -/
theorem convection_eLpNorm_two_le (v : Field) (hv : ContDiff ℝ ∞ v) :
    eLpNorm (convection v) 2 (volume.restrict unitCube) ≤
      eLpNorm v 6 (volume.restrict unitCube) *
        eLpNorm (fderiv ℝ v) 3 (volume.restrict unitCube) := by
  letI : ENNReal.HolderTriple 6 3 2 := by
    have h : Real.HolderTriple (6 : ℝ) 3 2 := by constructor <;> norm_num
    simpa using h.ennrealOfReal
  have hd : Continuous (fderiv ℝ v) :=
    (hv.fderiv_right (m := 0) (by norm_num)).continuous
  have h := eLpNorm_le_eLpNorm_mul_eLpNorm'_of_norm
    (μ := volume.restrict unitCube) (p := 6) (q := 3) (r := 2)
    hv.continuous.aestronglyMeasurable hd.aestronglyMeasurable
    (fun y : Vec => fun L : Vec →L[ℝ] Vec => L y) 1
    (Filter.Eventually.of_forall (fun x => by
      simpa only [NNReal.coe_one, one_mul, mul_comm] using
        (fderiv ℝ v x).le_opNorm (v x)))
  change eLpNorm (fun x => (fderiv ℝ v x) (v x)) 2 (volume.restrict unitCube) ≤ _
  simpa only [ENNReal.coe_one, one_mul] using h

theorem inner_integral_enorm_le_eLpNorm_two (v w : Field)
    (hv : Continuous v) (hw : Continuous w) :
    ENNReal.ofReal (abs (∫ x in unitCube, inner ℝ (v x) (w x))) ≤
      eLpNorm v 2 (volume.restrict unitCube) *
        eLpNorm w 2 (volume.restrict unitCube) := by
  have h := eLpNorm_le_eLpNorm_mul_eLpNorm'_of_norm
    (μ := volume.restrict unitCube) (p := 2) (q := 2) (r := 1)
    hv.aestronglyMeasurable hw.aestronglyMeasurable
    (fun y z : Vec => inner ℝ y z) 1
    (Filter.Eventually.of_forall (fun x => by
      simpa only [NNReal.coe_one, one_mul] using
        norm_inner_le_norm (𝕜 := ℝ) (v x) (w x)))
  calc
    _ = ‖(∫ x in unitCube, inner ℝ (v x) (w x))‖ₑ := by
      rw [← ofReal_norm, Real.norm_eq_abs]
    _ ≤ ∫⁻ x, ‖inner ℝ (v x) (w x)‖ₑ ∂volume.restrict unitCube :=
      enorm_integral_le_lintegral_enorm _
    _ = eLpNorm (fun x => inner ℝ (v x) (w x)) 1 (volume.restrict unitCube) :=
      (eLpNorm_one_eq_lintegral_enorm (f := fun x => inner ℝ (v x) (w x))).symm
    _ ≤ _ := by simpa only [ENNReal.coe_one, one_mul] using h

theorem ennreal_three_quarter_product (A B E Z : ℝ≥0∞) :
    ((A * E ^ (1 / 2 : ℝ)) *
        (((3 : ℝ≥0∞) ^ (1 / 2 : ℝ) * E ^ (1 / 2 : ℝ)) ^ (1 / 2 : ℝ) *
          (B * Z ^ (1 / 2 : ℝ)) ^ (1 / 2 : ℝ))) * Z ^ (1 / 2 : ℝ) =
      (A * (3 : ℝ≥0∞) ^ (1 / 4 : ℝ) * B ^ (1 / 2 : ℝ)) *
        E ^ (3 / 4 : ℝ) * Z ^ (3 / 4 : ℝ) := by
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  simp only [← ENNReal.rpow_mul]
  norm_num
  calc
    _ = (A * (3 : ℝ≥0∞) ^ (1 / 4 : ℝ) * B ^ (1 / 2 : ℝ)) *
        (E ^ (1 / 2 : ℝ) * E ^ (1 / 4 : ℝ)) *
        (Z ^ (1 / 4 : ℝ) * Z ^ (1 / 2 : ℝ)) := by ring
    _ = _ := by
      rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num),
        ← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
      norm_num

/-- The physical convection/Laplacian pairing satisfies the cutoff-independent
three-quarter-power estimate. The physical field and every derivative are literal. -/
theorem FINITE_PHYSICAL_NONLINEAR_THREE_QUARTER_BOUND :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ N : ℕ, ∀ c : FourierCoeff, SpectralReality c →
      ENNReal.ofReal (abs (∫ x in unitCube,
        inner ℝ (convection (finiteSynthesis N c) x) (laplacian (finiteSynthesis N c) x))) ≤
          C * (ENNReal.ofReal (coefficientDissipation N c)) ^ (3 / 4 : ℝ) *
            (ENNReal.ofReal (coefficientLaplacianSquare N c)) ^ (3 / 4 : ℝ) := by
  obtain ⟨A, hA, hSob⟩ := FINITE_PHYSICAL_L6_FROM_ENSTROPHY
  obtain ⟨B, hB, hDeriv⟩ := FINITE_PHYSICAL_DERIVATIVE_L6_FROM_LAPLACIAN
  refine ⟨A * (3 : ℝ≥0∞) ^ (1 / 4 : ℝ) * B ^ (1 / 2 : ℝ),
    by finiteness, ?_⟩
  intro N c hreal
  have hv := finiteSynthesis_contDiff N c
  have hd : Continuous (fderiv ℝ (finiteSynthesis N c)) :=
    (hv.fderiv_right (m := 0) (by norm_num)).continuous
  have hconv : Continuous (convection (finiteSynthesis N c)) :=
    hd.clm_apply hv.continuous
  have hlap : Continuous (laplacian (finiteSynthesis N c)) := by
    rw [finiteSynthesis_laplacian]
    exact (finiteSynthesis_contDiff N _).continuous
  have hD3 := cube_eLpNorm_three_le_interpolation (fderiv ℝ (finiteSynthesis N c)) hd
  have hD2 := finite_fderiv_eLpNorm_two_le N c hreal
  have hD6 := hDeriv N c hreal
  have hV6 := hSob N c hreal
  calc
    _ ≤ eLpNorm (convection (finiteSynthesis N c)) 2 (volume.restrict unitCube) *
        eLpNorm (laplacian (finiteSynthesis N c)) 2 (volume.restrict unitCube) :=
      inner_integral_enorm_le_eLpNorm_two _ _ hconv hlap
    _ ≤ (eLpNorm (finiteSynthesis N c) 6 (volume.restrict unitCube) *
        eLpNorm (fderiv ℝ (finiteSynthesis N c)) 3 (volume.restrict unitCube)) *
        (ENNReal.ofReal (coefficientLaplacianSquare N c)) ^ (1 / 2 : ℝ) := by
      rw [finite_laplacian_eLpNorm_two N c hreal]
      exact mul_le_mul_of_nonneg_right (convection_eLpNorm_two_le _ hv) bot_le
    _ ≤ ((A * (ENNReal.ofReal (coefficientDissipation N c)) ^ (1 / 2 : ℝ)) *
        (((3 : ℝ≥0∞) ^ (1 / 2 : ℝ) *
            (ENNReal.ofReal (coefficientDissipation N c)) ^ (1 / 2 : ℝ)) ^ (1 / 2 : ℝ) *
          (B * (ENNReal.ofReal (coefficientLaplacianSquare N c)) ^ (1 / 2 : ℝ)) ^
            (1 / 2 : ℝ))) *
        (ENNReal.ofReal (coefficientLaplacianSquare N c)) ^ (1 / 2 : ℝ) := by
      apply mul_le_mul_of_nonneg_right _ bot_le
      refine mul_le_mul hV6 ?_ bot_le bot_le
      exact hD3.trans (mul_le_mul
        (ENNReal.rpow_le_rpow hD2 (by norm_num))
        (ENNReal.rpow_le_rpow hD6 (by norm_num)) bot_le bot_le)
    _ = _ := ennreal_three_quarter_product _ _ _ _

end

end SingularClosure
