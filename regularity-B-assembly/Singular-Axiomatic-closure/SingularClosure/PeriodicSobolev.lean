import SingularClosure.PeriodicPoincare
import SingularClosure.PeriodicCover

/-!
# A concrete compact-support Sobolev transfer on the physical unit cube

The fixed smooth cutoff equals one on the physical cube and vanishes outside
the ball of radius three. Its derivative is bounded by one fixed finite
constant. Mathlib's whole-space GNS inequality therefore gives a local
L6--H1 inequality with constants independent of every Fourier cutoff.

The proved finite periodic cover reduces the radius-three norms to cube
norms. This module is an auxiliary toward frozen endpoint 5, not a proof
of its nonlinear estimate.
-/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory Metric
open scoped ContDiff ENNReal NNReal BigOperators

namespace SingularClosure

noncomputable section

def unitCubeSobolevBump : ContDiffBump (0 : Vec) :=
  ⟨2, 3, by norm_num, by norm_num⟩

theorem unitCube_subset_closedBall_two :
    unitCube ⊆ closedBall (0 : Vec) 2 := by
  intro x hx
  rw [mem_closedBall, dist_zero_right]
  have hsq (i : Fin 3) : (x i) ^ 2 ≤ 1 := by
    have hi := hx i
    nlinarith [mul_nonneg hi.1 (sub_nonneg.mpr hi.2)]
  have hnorm : ‖x‖ ^ 2 ≤ 3 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [Fin.sum_univ_succ]
    nlinarith [hsq 0, hsq 1, hsq 2]
  nlinarith [norm_nonneg x]

theorem unitCubeSobolevBump_eq_one {x : Vec} (hx : x ∈ unitCube) :
    unitCubeSobolevBump x = 1 :=
  unitCubeSobolevBump.one_of_mem_closedBall (unitCube_subset_closedBall_two hx)

theorem unitCubeSobolevBump_derivative_bound :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ x : Vec, ‖fderiv ℝ (unitCubeSobolevBump : Vec → ℝ) x‖ ≤ K := by
  have hc : Continuous (fderiv ℝ (unitCubeSobolevBump : Vec → ℝ)) :=
    ((unitCubeSobolevBump.contDiff (n := ∞)).fderiv_right (m := 0) (by norm_num)).continuous
  have hs : HasCompactSupport (fderiv ℝ (unitCubeSobolevBump : Vec → ℝ)) :=
    unitCubeSobolevBump.hasCompactSupport.fderiv ℝ
  obtain ⟨K, hK⟩ := hs.exists_bound_of_continuous hc
  exact ⟨max K 0, le_max_right K 0,
    fun x => (hK x).trans (le_max_left K 0)⟩

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

def unitCubeCutoff (v : Vec → F) : Vec → F :=
  fun x => unitCubeSobolevBump x • v x

theorem unitCubeCutoff_eqOn (v : Vec → F) : EqOn (unitCubeCutoff v) v unitCube := by
  intro x hx
  simp only [unitCubeCutoff, unitCubeSobolevBump_eq_one hx, one_smul]

theorem unitCubeCutoff_contDiff {v : Vec → F} (hv : ContDiff ℝ ∞ v) :
    ContDiff ℝ ∞ (unitCubeCutoff v) :=
  unitCubeSobolevBump.contDiff.smul hv

theorem unitCubeCutoff_hasCompactSupport (v : Vec → F) :
    HasCompactSupport (unitCubeCutoff v) :=
  unitCubeSobolevBump.hasCompactSupport.smul_right

theorem unitCubeCutoff_tsupport_subset (v : Vec → F) :
    tsupport (unitCubeCutoff v) ⊆ closedBall (0 : Vec) 3 := by
  have h := tsupport_smul_subset_left (unitCubeSobolevBump : Vec → ℝ) v
  rw [unitCubeSobolevBump.tsupport_eq] at h
  exact h

theorem unitCubeCutoff_fderiv_support_subset (v : Vec → F) :
    Function.support (fderiv ℝ (unitCubeCutoff v)) ⊆ closedBall (0 : Vec) 3 :=
  (support_fderiv_subset ℝ).trans (unitCubeCutoff_tsupport_subset v)

theorem unitCubeCutoff_fderiv_norm_le {v : Vec → F} (hv : ContDiff ℝ ∞ v)
    {K : ℝ} (hK : ∀ x : Vec, ‖fderiv ℝ (unitCubeSobolevBump : Vec → ℝ) x‖ ≤ K)
    (x : Vec) :
    ‖fderiv ℝ (unitCubeCutoff v) x‖ ≤ ‖fderiv ℝ v x‖ + K * ‖v x‖ := by
  have hχ : DifferentiableAt ℝ (unitCubeSobolevBump : Vec → ℝ) x :=
    (unitCubeSobolevBump.contDiff (n := ∞)).differentiable (by norm_num) x
  have hvx : DifferentiableAt ℝ v x := hv.differentiable (by norm_num) x
  have hχnorm : ‖unitCubeSobolevBump x‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg unitCubeSobolevBump.nonneg]
    exact unitCubeSobolevBump.le_one
  rw [unitCubeCutoff, fderiv_fun_smul hχ hvx]
  calc
    _ ≤ ‖unitCubeSobolevBump x • fderiv ℝ v x‖ +
        ‖(fderiv ℝ (unitCubeSobolevBump : Vec → ℝ) x).smulRight (v x)‖ :=
      norm_add_le _ _
    _ = ‖unitCubeSobolevBump x‖ * ‖fderiv ℝ v x‖ +
        ‖fderiv ℝ (unitCubeSobolevBump : Vec → ℝ) x‖ * ‖v x‖ := by
      rw [norm_smul, ContinuousLinearMap.norm_smulRight_apply]
    _ ≤ 1 * ‖fderiv ℝ v x‖ + K * ‖v x‖ :=
      add_le_add (mul_le_mul_of_nonneg_right hχnorm (norm_nonneg _))
        (mul_le_mul_of_nonneg_right (hK x) (norm_nonneg _))
    _ = _ := by rw [one_mul]

theorem unitCubeCutoff_fderiv_eLpNorm_le {v : Vec → F} (hv : ContDiff ℝ ∞ v)
    {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ x : Vec, ‖fderiv ℝ (unitCubeSobolevBump : Vec → ℝ) x‖ ≤ K) :
    eLpNorm (fderiv ℝ (unitCubeCutoff v)) 2 volume ≤
      eLpNorm (fderiv ℝ v) 2 (volume.restrict (closedBall (0 : Vec) 3)) +
        ENNReal.ofReal K * eLpNorm v 2 (volume.restrict (closedBall (0 : Vec) 3)) := by
  let μ : Measure Vec := volume.restrict (closedBall (0 : Vec) 3)
  have hd : Continuous (fderiv ℝ v) :=
    (hv.fderiv_right (m := 0) (by norm_num)).continuous
  rw [← eLpNorm_restrict_eq_of_support_subset (unitCubeCutoff_fderiv_support_subset v)]
  calc
    eLpNorm (fderiv ℝ (unitCubeCutoff v)) 2 μ ≤
        eLpNorm (fun x => ‖fderiv ℝ v x‖ + K * ‖v x‖) 2 μ :=
      eLpNorm_mono_real (unitCubeCutoff_fderiv_norm_le hv hK)
    _ ≤ eLpNorm (fun x => ‖fderiv ℝ v x‖) 2 μ +
        eLpNorm (fun x => K * ‖v x‖) 2 μ :=
      eLpNorm_add_le hd.norm.aestronglyMeasurable
        (continuous_const.mul hv.continuous.norm).aestronglyMeasurable (by norm_num)
    _ = _ := by
      rw [eLpNorm_norm]
      have hsmul : (fun x => K * ‖v x‖) = K • (fun x => ‖v x‖) := rfl
      rw [hsmul, eLpNorm_const_smul, eLpNorm_norm]
      rw [Real.enorm_eq_ofReal hK0]

/-- A true local Sobolev transfer with constants independent of the field.
The remaining periodic-cover step concerns the two radius-three norms. -/
theorem UNIT_CUBE_SOBOLEV_CUTOFF_TRANSFER [FiniteDimensional ℝ F] :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ v : Vec → F, ContDiff ℝ ∞ v →
      eLpNorm v 6 (volume.restrict unitCube) ≤
        (SNormLESNormFDerivOfEqConst F (volume : Measure Vec) 2 : ℝ≥0∞) *
          (eLpNorm (fderiv ℝ v) 2 (volume.restrict (closedBall (0 : Vec) 3)) +
            ENNReal.ofReal K * eLpNorm v 2 (volume.restrict (closedBall (0 : Vec) 3))) := by
  obtain ⟨K, hK0, hK⟩ := unitCubeSobolevBump_derivative_bound
  refine ⟨K, hK0, ?_⟩
  intro v hv
  have heq : v =ᵐ[volume.restrict unitCube] unitCubeCutoff v := by
    filter_upwards [ae_restrict_mem isCompact_unitCube.measurableSet] with x hx
    exact (unitCubeCutoff_eqOn v hx).symm
  have hGNS := MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_eq
    (μ := (volume : Measure Vec)) (F := F)
    ((unitCubeCutoff_contDiff hv).of_le (by norm_num))
    (unitCubeCutoff_hasCompactSupport v)
    (p := (2 : ℝ≥0)) (p' := (6 : ℝ≥0)) (by norm_num)
    (by simp [Vec]) (by simp [Vec]; norm_num)
  calc
    _ = eLpNorm (unitCubeCutoff v) 6 (volume.restrict unitCube) := eLpNorm_congr_ae heq
    _ ≤ eLpNorm (unitCubeCutoff v) 6 volume :=
      eLpNorm_mono_measure _ Measure.restrict_le_self
    _ ≤ _ := hGNS.trans (mul_le_mul_left'
      (unitCubeCutoff_fderiv_eLpNorm_le hv hK0 hK) _)

theorem spatialPeriodic_fderiv {v : Vec → F} (hp : SpatialPeriodic v) :
    SpatialPeriodic (fderiv ℝ v) := by
  intro x i
  have heq : (fun y : Vec => v (y + unitVector i)) = v :=
    funext (fun y => hp y i)
  have h := congrArg (fun w : Vec → F => fderiv ℝ w x) heq
  simpa only [fderiv_comp_add_right] using h

theorem eLpNorm_two_eq_integral_norm_sq_rpow
    (v : Vec → F) (μ : Measure Vec)
    (hi : Integrable (fun x => ‖v x‖ ^ 2) μ) :
    eLpNorm v 2 μ =
      (ENNReal.ofReal (∫ x, ‖v x‖ ^ 2 ∂μ)) ^ (1 / 2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  norm_num only [ENNReal.toReal_ofNat]
  rw [ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall (fun x => sq_nonneg ‖v x‖))]
  congr 1
  apply lintegral_congr
  intro x
  rw [ENNReal.rpow_natCast, ← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _) 2]

/-- The finite cover gives one L2 constant for every continuous periodic map. -/
theorem periodic_closedBall_three_eLpNorm_two_le (v : Vec → F)
    (hv : Continuous v) (hp : SpatialPeriodic v) :
    eLpNorm v 2 (volume.restrict (closedBall (0 : Vec) 3)) ≤
      (343 : ℝ≥0∞) ^ (1 / 2 : ℝ) * eLpNorm v 2 (volume.restrict unitCube) := by
  have hcont : Continuous (fun x : Vec => ‖v x‖ ^ 2) := hv.norm.pow 2
  have hperiod : SpatialPeriodic (fun x : Vec => ‖v x‖ ^ 2) := by
    intro x i
    rw [hp x i]
  have hbound := periodic_closedBall_three_integral_le
    (fun x : Vec => ‖v x‖ ^ 2) hcont hperiod (fun x => sq_nonneg _)
  have hball : Integrable (fun x : Vec => ‖v x‖ ^ 2)
      (volume.restrict (closedBall (0 : Vec) 3)) :=
    hcont.continuousOn.integrableOn_compact (isCompact_closedBall _ _)
  have hcube : Integrable (fun x : Vec => ‖v x‖ ^ 2) (volume.restrict unitCube) :=
    hcont.continuousOn.integrableOn_compact isCompact_unitCube
  rw [eLpNorm_two_eq_integral_norm_sq_rpow v _ hball,
    eLpNorm_two_eq_integral_norm_sq_rpow v _ hcube]
  calc
    _ ≤ (ENNReal.ofReal (343 * ∫ x in unitCube, ‖v x‖ ^ 2)) ^ (1 / 2 : ℝ) :=
      ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hbound) (by norm_num)
    _ = _ := by
      rw [ENNReal.ofReal_mul (by norm_num),
        ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
      norm_num

/-- Actual periodic H1-to-L6 bound, including the lower-order L2 term.
Both constants are fixed before the function quantifier. -/
theorem PERIODIC_SOBOLEV_H1_L6 [FiniteDimensional ℝ F] :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ v : Vec → F, ContDiff ℝ ∞ v → SpatialPeriodic v →
      eLpNorm v 6 (volume.restrict unitCube) ≤
        (SNormLESNormFDerivOfEqConst F (volume : Measure Vec) 2 : ℝ≥0∞) *
          (343 : ℝ≥0∞) ^ (1 / 2 : ℝ) *
          (eLpNorm (fderiv ℝ v) 2 (volume.restrict unitCube) +
            ENNReal.ofReal K * eLpNorm v 2 (volume.restrict unitCube)) := by
  obtain ⟨K, hK0, hK⟩ := UNIT_CUBE_SOBOLEV_CUTOFF_TRANSFER (F := F)
  refine ⟨K, hK0, ?_⟩
  intro v hv hp
  have hd : Continuous (fderiv ℝ v) :=
    (hv.fderiv_right (m := 0) (by norm_num)).continuous
  have hD := periodic_closedBall_three_eLpNorm_two_le (fderiv ℝ v)
    hd (spatialPeriodic_fderiv hp)
  have hV := periodic_closedBall_three_eLpNorm_two_le v hv.continuous hp
  calc
    _ ≤ _ := hK v hv
    _ ≤ (SNormLESNormFDerivOfEqConst F (volume : Measure Vec) 2 : ℝ≥0∞) *
        ((343 : ℝ≥0∞) ^ (1 / 2 : ℝ) * eLpNorm (fderiv ℝ v) 2 (volume.restrict unitCube) +
          ENNReal.ofReal K * ((343 : ℝ≥0∞) ^ (1 / 2 : ℝ) *
            eLpNorm v 2 (volume.restrict unitCube))) :=
      mul_le_mul_left' (add_le_add hD (mul_le_mul_left' hV _)) _
    _ = _ := by ring

theorem sum_coordinate_unitVector (x : Vec) :
    (∑ i : Fin 3, x i • unitVector i) = x := by
  ext j
  fin_cases j <;> simp [unitVector, Fin.sum_univ_succ, Pi.single_apply]

theorem opNorm_le_sum_coordinate_norm (L : Vec →L[ℝ] F) :
    ‖L‖ ≤ ∑ i : Fin 3, ‖L (unitVector i)‖ := by
  apply L.opNorm_le_bound (Finset.sum_nonneg (fun i _ => norm_nonneg _))
  intro x
  have hrepr : L x = ∑ i : Fin 3, x i • L (unitVector i) := by
    have h := congrArg L (sum_coordinate_unitVector x)
    simpa only [map_sum, map_smul] using h.symm
  rw [hrepr]
  calc
    _ ≤ ∑ i : Fin 3, ‖x i • L (unitVector i)‖ := norm_sum_le _ _
    _ = ∑ i : Fin 3, ‖x i‖ * ‖L (unitVector i)‖ := by simp only [norm_smul]
    _ ≤ ∑ i : Fin 3, ‖x‖ * ‖L (unitVector i)‖ := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_right (PiLp.norm_apply_le x i) (norm_nonneg _)
    _ = _ := by rw [← Finset.mul_sum, mul_comm]

theorem opNorm_sq_le_three_sum_coordinate_sq (L : Vec →L[ℝ] F) :
    ‖L‖ ^ 2 ≤ 3 * ∑ i : Fin 3, ‖L (unitVector i)‖ ^ 2 := by
  have hsum : 0 ≤ ∑ i : Fin 3, ‖L (unitVector i)‖ :=
    Finset.sum_nonneg (fun i _ => norm_nonneg _)
  have hsq := (sq_le_sq₀ (norm_nonneg L) hsum).mpr (opNorm_le_sum_coordinate_norm L)
  have hCS := sq_sum_le_card_mul_sum_sq
    (s := Finset.univ) (f := fun i : Fin 3 => ‖L (unitVector i)‖)
  exact hsq.trans (by simpa using hCS)

theorem fderiv_norm_sq_le_three_gradientSquareDensity (v : Field) (x : Vec) :
    ‖fderiv ℝ v x‖ ^ 2 ≤ 3 * gradientSquareDensity v x := by
  simpa only [gradientSquareDensity_eq_sum_norm_sq, coordinateDerivative] using
    opNorm_sq_le_three_sum_coordinate_sq (fderiv ℝ v x)

theorem finite_fderiv_eLpNorm_two_le (N : ℕ) (c : FourierCoeff)
    (hreal : SpectralReality c) :
    eLpNorm (fderiv ℝ (finiteSynthesis N c)) 2 (volume.restrict unitCube) ≤
      (3 : ℝ≥0∞) ^ (1 / 2 : ℝ) *
        (ENNReal.ofReal (coefficientDissipation N c)) ^ (1 / 2 : ℝ) := by
  have hv := finiteSynthesis_contDiff N c
  have hd : Continuous (fderiv ℝ (finiteSynthesis N c)) :=
    (hv.fderiv_right (m := 0) (by norm_num)).continuous
  have hi : IntegrableOn (fun x => ‖fderiv ℝ (finiteSynthesis N c) x‖ ^ 2)
      unitCube volume :=
    (hd.norm.pow 2).continuousOn.integrableOn_compact isCompact_unitCube
  have hI : (∫ x in unitCube, ‖fderiv ℝ (finiteSynthesis N c) x‖ ^ 2) ≤
      3 * coefficientDissipation N c := by
    calc
      _ ≤ ∫ x in unitCube, 3 * gradientSquareDensity (finiteSynthesis N c) x :=
        integral_mono hi ((gradientSquareDensity_integrableOn hv).const_mul 3)
          (fun x => fderiv_norm_sq_le_three_gradientSquareDensity _ x)
      _ = _ := by
        rw [integral_const_mul, FINITE_PHYSICAL_REAL_ENSTROPHY_PARSEVAL N c hreal]
  rw [eLpNorm_two_eq_integral_norm_sq_rpow _ _ hi]
  calc
    _ ≤ (ENNReal.ofReal (3 * coefficientDissipation N c)) ^ (1 / 2 : ℝ) :=
      ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hI) (by norm_num)
    _ = _ := by
      rw [ENNReal.ofReal_mul (by norm_num),
        ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
      norm_num

theorem coefficientEnergy_le_dissipation (N : ℕ) (c : FourierCoeff) :
    coefficientEnergy N c ≤ coefficientDissipation N c := by
  have hgap : (1 : ℝ) ≤ 4 * Real.pi ^ 2 := by
    nlinarith [Real.pi_gt_three]
  calc
    coefficientEnergy N c = 1 * coefficientEnergy N c := by ring
    _ ≤ 4 * Real.pi ^ 2 * coefficientEnergy N c :=
      mul_le_mul_of_nonneg_right hgap (coefficientEnergy_nonneg N c)
    _ ≤ coefficientDissipation N c := COEFFICIENT_POINCARE N c

theorem finite_eLpNorm_two_le_enstrophy (N : ℕ) (c : FourierCoeff)
    (hreal : SpectralReality c) :
    eLpNorm (finiteSynthesis N c) 2 (volume.restrict unitCube) ≤
      (ENNReal.ofReal (coefficientDissipation N c)) ^ (1 / 2 : ℝ) := by
  have hi : IntegrableOn (fun x => ‖finiteSynthesis N c x‖ ^ 2) unitCube volume :=
    ((finiteSynthesis_contDiff N c).continuous.norm.pow 2).continuousOn
      .integrableOn_compact isCompact_unitCube
  rw [eLpNorm_two_eq_integral_norm_sq_rpow _ _ hi]
  rw [← physicalEnergy_eq_integral_norm_sq, FINITE_PHYSICAL_ENERGY_PARSEVAL N c hreal]
  exact ENNReal.rpow_le_rpow
    (ENNReal.ofReal_le_ofReal (coefficientEnergy_le_dissipation N c)) (by norm_num)

/-- Actual mean-zero finite Fourier Sobolev estimate, with one finite constant
for every cutoff and coefficient family. No Sobolev certificate is assumed. -/
theorem FINITE_PHYSICAL_L6_FROM_ENSTROPHY :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ N : ℕ, ∀ c : FourierCoeff, SpectralReality c →
      eLpNorm (finiteSynthesis N c) 6 (volume.restrict unitCube) ≤
        C * (ENNReal.ofReal (coefficientDissipation N c)) ^ (1 / 2 : ℝ) := by
  obtain ⟨K, hK0, hK⟩ := PERIODIC_SOBOLEV_H1_L6 (F := Vec)
  let C : ℝ≥0∞ :=
    (SNormLESNormFDerivOfEqConst Vec (volume : Measure Vec) 2 : ℝ≥0∞) *
      (343 : ℝ≥0∞) ^ (1 / 2 : ℝ) *
        ((3 : ℝ≥0∞) ^ (1 / 2 : ℝ) + ENNReal.ofReal K)
  have hC : C < ⊤ := by
    dsimp [C]
    finiteness
  refine ⟨C, hC, ?_⟩
  intro N c hreal
  have hD := finite_fderiv_eLpNorm_two_le N c hreal
  have hV := finite_eLpNorm_two_le_enstrophy N c hreal
  calc
    _ ≤ _ := hK (finiteSynthesis N c) (finiteSynthesis_contDiff N c)
      (finiteSynthesis_periodic N c)
    _ ≤ (SNormLESNormFDerivOfEqConst Vec (volume : Measure Vec) 2 : ℝ≥0∞) *
        (343 : ℝ≥0∞) ^ (1 / 2 : ℝ) *
        ((3 : ℝ≥0∞) ^ (1 / 2 : ℝ) *
          (ENNReal.ofReal (coefficientDissipation N c)) ^ (1 / 2 : ℝ) +
          ENNReal.ofReal K *
            (ENNReal.ofReal (coefficientDissipation N c)) ^ (1 / 2 : ℝ)) :=
      mul_le_mul_left' (add_le_add hD (mul_le_mul_left' hV _)) _
    _ = _ := by dsimp [C]; ring

end

end SingularClosure
