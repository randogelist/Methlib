import SingularClosure.CriticalNegativeEnergy
import SingularClosure.CriticalHolder
import SingularClosure.CriticalSobolev

/-! Actual negative-half-order transport control by finite duality.
The test field is Λ⁻¹ of the projected transport itself. The physical
exponents are 6, 2, 3; no two-critical nonsymmetric trilinear estimate is used. -/

set_option autoImplicit false
set_option Elab.async true

noncomputable section

open Set MeasureTheory
open scoped ContDiff ENNReal NNReal BigOperators

namespace SingularClosure

theorem convection_eLpNorm_threeHalves_le (v : Field) (hv : ContDiff ℝ ∞ v) :
    eLpNorm (convection v) (3 / 2) (volume.restrict unitCube) ≤
      eLpNorm v 6 (volume.restrict unitCube) *
        eLpNorm (fderiv ℝ v) 2 (volume.restrict unitCube) := by
  letI : ENNReal.HolderTriple 6 2 (3 / 2) := by
    have h : Real.HolderTriple (6 : ℝ) 2 (3 / 2) := by constructor <;> norm_num
    simpa using h.ennrealOfReal
  have hd : Continuous (fderiv ℝ v) :=
    (hv.fderiv_right (m := 0) (by norm_num)).continuous
  have h := eLpNorm_le_eLpNorm_mul_eLpNorm'_of_norm
    (μ := volume.restrict unitCube) (p := 6) (q := 2) (r := 3 / 2)
    hv.continuous.aestronglyMeasurable hd.aestronglyMeasurable
    (fun y : Vec => fun L : Vec →L[ℝ] Vec => L y) 1
    (Filter.Eventually.of_forall (fun x => by
      simpa only [NNReal.coe_one, one_mul, mul_comm] using
        (fderiv ℝ v x).le_opNorm (v x)))
  change eLpNorm (fun x => (fderiv ℝ v x) (v x)) (3 / 2)
    (volume.restrict unitCube) ≤ _
  simpa only [ENNReal.coe_one, one_mul] using h

theorem inner_integral_enorm_le_eLpNorm_three_threeHalves (v w : Field)
    (hv : Continuous v) (hw : Continuous w) :
    ENNReal.ofReal (abs (∫ x in unitCube, inner ℝ (v x) (w x))) ≤
      eLpNorm v 3 (volume.restrict unitCube) *
        eLpNorm w (3 / 2) (volume.restrict unitCube) := by
  letI : ENNReal.HolderTriple 3 (3 / 2) 1 := by
    have h : Real.HolderTriple (3 : ℝ) (3 / 2) 1 := by constructor <;> norm_num
    simpa using h.ennrealOfReal
  have h := eLpNorm_le_eLpNorm_mul_eLpNorm'_of_norm
    (μ := volume.restrict unitCube) (p := 3) (q := 3 / 2) (r := 1)
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

theorem ennreal_negative_holder_product (S A X E : ℝ≥0∞) :
    (S * E ^ (1 / 2 : ℝ)) *
      ((A * X ^ (1 / 2 : ℝ)) * ((3 : ℝ≥0∞) ^ (1 / 2 : ℝ) * X ^ (1 / 2 : ℝ))) =
    (S * A * (3 : ℝ≥0∞) ^ (1 / 2 : ℝ)) * X * E ^ (1 / 2 : ℝ) := by
  calc
    _ = (S * A * (3 : ℝ≥0∞) ^ (1 / 2 : ℝ)) *
        (X ^ (1 / 2 : ℝ) * X ^ (1 / 2 : ℝ)) * E ^ (1 / 2 : ℝ) := by ring
    _ = _ := by
      rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
      norm_num

/-- The actual projected transport satisfies the cutoff-independent
negative-half-order estimate. -/
theorem FINITE_CRITICAL_NEGATIVE_TRANSPORT_BOUND :
    ∃ D : ℝ, 0 < D ∧ ∀ N : ℕ, ∀ c : FourierCoeff,
      (∀ k : Frequency, k ∉ cutoffModes N → ∀ i : Fin 3, c k i = 0) →
      SpectralReality c →
      ‖criticalFiniteSobolev (-1) N (criticalProjectedTransport N c)‖ ≤
        D * criticalEnergy 2 N c := by
  obtain ⟨S, hS, hSob3⟩ := FINITE_CRITICAL_HHALF_L3
  obtain ⟨A, hA, hSob6⟩ := FINITE_PHYSICAL_L6_FROM_ENSTROPHY
  let K : ℝ≥0∞ := S * A * (3 : ℝ≥0∞) ^ (1 / 2 : ℝ)
  have hK : K < ⊤ := by dsimp [K]; finiteness
  refine ⟨K.toReal + 1, by positivity, ?_⟩
  intro N c hsupp hreal
  let b : FourierCoeff := criticalProjectedTransport N c
  let v : Field := finiteSynthesis N (criticalInverseLambdaCoefficient b)
  let E : ℝ := criticalNegativeEnergy N b
  let X : ℝ := criticalEnergy 2 N c
  have hE : 0 ≤ E := criticalNegativeEnergy_nonneg N b
  have hX : 0 ≤ X := criticalEnergy_nonneg 2 N c
  have htest : eLpNorm v 3 (volume.restrict unitCube) ≤
      S * (ENNReal.ofReal E) ^ (1 / 2 : ℝ) := by
    simpa only [v, E, criticalEnergy_one_inverseLambda] using
      hSob3 N (criticalInverseLambdaCoefficient b)
  have hu6 : eLpNorm (finiteSynthesis N c) 6 (volume.restrict unitCube) ≤
      A * (ENNReal.ofReal X) ^ (1 / 2 : ℝ) := by
    simpa only [X, criticalEnergy_two_eq_coefficientDissipation] using hSob6 N c hreal
  have hd2 : eLpNorm (fderiv ℝ (finiteSynthesis N c)) 2 (volume.restrict unitCube) ≤
      (3 : ℝ≥0∞) ^ (1 / 2 : ℝ) * (ENNReal.ofReal X) ^ (1 / 2 : ℝ) := by
    simpa only [X, criticalEnergy_two_eq_coefficientDissipation] using
      finite_fderiv_eLpNorm_two_le N c hreal
  have hpair : (∫ x in unitCube, inner ℝ (v x) (convection (finiteSynthesis N c) x)) = E :=
    criticalInverseLambda_transport_pairing N c hsupp hreal
  have hbound : ENNReal.ofReal E ≤ K * ENNReal.ofReal X *
      (ENNReal.ofReal E) ^ (1 / 2 : ℝ) := by
    calc
      _ = ENNReal.ofReal (abs (∫ x in unitCube,
          inner ℝ (v x) (convection (finiteSynthesis N c) x))) := by
        rw [hpair, abs_of_nonneg hE]
      _ ≤ eLpNorm v 3 (volume.restrict unitCube) *
          eLpNorm (convection (finiteSynthesis N c)) (3 / 2) (volume.restrict unitCube) :=
        inner_integral_enorm_le_eLpNorm_three_threeHalves _ _
          (finiteSynthesis_contDiff N _).continuous
          (convection_continuous (finiteSynthesis_contDiff N c))
      _ ≤ (S * (ENNReal.ofReal E) ^ (1 / 2 : ℝ)) *
          ((A * (ENNReal.ofReal X) ^ (1 / 2 : ℝ)) *
            ((3 : ℝ≥0∞) ^ (1 / 2 : ℝ) * (ENNReal.ofReal X) ^ (1 / 2 : ℝ))) := by
        apply mul_le_mul htest _ bot_le bot_le
        exact (convection_eLpNorm_threeHalves_le _ (finiteSynthesis_contDiff N c)).trans
          (mul_le_mul hu6 hd2 bot_le bot_le)
      _ = _ := ennreal_negative_holder_product S A _ _
  have hr := ENNReal.toReal_mono (by finiteness) hbound
  simp only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal hE, ENNReal.toReal_ofReal hX, Real.rpow_one_half] at hr
  let z : CriticalSobolev (-1) := criticalFiniteSobolev (-1) N b
  have hzsq : ‖z‖ ^ 2 = E := criticalFiniteSobolev_neg_one_norm_sq N b
  have hsqrt : Real.sqrt E = ‖z‖ := by rw [← hzsq, Real.sqrt_sq (norm_nonneg z)]
  rw [hsqrt, ← hzsq] at hr
  have hz : ‖z‖ ≤ K.toReal * X := by
    by_cases hzero : ‖z‖ = 0
    · rw [hzero]
      exact mul_nonneg ENNReal.toReal_nonneg hX
    · have hpos : 0 < ‖z‖ := lt_of_le_of_ne (norm_nonneg z) (Ne.symm hzero)
      by_contra hnot
      have hp := mul_pos (sub_pos.mpr (lt_of_not_ge hnot)) hpos
      nlinarith only [hr, hp]
  calc
    _ ≤ K.toReal * X := hz
    _ ≤ (K.toReal + 1) * X := mul_le_mul_of_nonneg_right (by linarith) hX

end SingularClosure
