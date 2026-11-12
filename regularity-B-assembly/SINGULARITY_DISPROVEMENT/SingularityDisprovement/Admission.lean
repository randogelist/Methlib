import SingularClosure.NSE_H12_SIGMA_ZERO_SMALL_UNCONDITIONAL

/-! Actual calibrated admission on the native periodic critical Sobolev carrier.
No hypothesis contains a solution or an energy gap.  The gap is proved from
the nonzero lattice frequencies and the native Fourier representation. -/

set_option autoImplicit false
set_option Elab.async true

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal Interval

namespace SingularityDisprovement

open SingularClosure

noncomputable section

def physicalL2Map : CriticalSobolev 1 →L[ℝ] PhysicalCubeL2 :=
  torusToPhysicalCubeL2.comp ((criticalPhysicalL2 1 (by norm_num)).restrictScalars ℝ)

def physicalL2 (a : CriticalSobolev 1) : PhysicalCubeL2 := physicalL2Map a

theorem physicalL2_eq_native (a : CriticalSobolev 1) :
    physicalL2 a = criticalInitialPhysicalL2 a := rfl

@[simp]
theorem physicalL2_smul (r : ℝ) (a : CriticalSobolev 1) :
    physicalL2 (r • a) = r • physicalL2 a := physicalL2Map.map_smul r a

def kineticDensity (a : CriticalSobolev 1) (x : Vec) : ℝ :=
  ‖physicalL2 a x‖ ^ 2 / 2

def EssUnbounded (a : CriticalSobolev 1) : Prop :=
  ∀ M : ℝ, 0 ≤ M →
    0 < (volume.restrict unitCube) {x | M < kineticDensity a x}

def calibrationGamma : ℝ := 1 - 5 / (4 * Real.pi)

def calibrationCap : ℝ :=
  min Real.pi (calibrationGamma / (4 * criticalNonlinearConstant ^ 2))

def shiftedEnergy (ν : ℝ) (a : CriticalSobolev 1) : ℝ :=
  (‖a‖ ^ 2 - (5 / 2 : ℝ) * ‖physicalL2 a‖ ^ 2) / (2 * ν ^ 2)

def calibratedScore (ν : ℝ) (a : CriticalSobolev 1) : ℝ :=
  (Real.pi / calibrationCap) * shiftedEnergy ν a

def stageZeroBudget : ℝ := 2

/-- The complete conclusion of the imported, audited native theorem. -/
def Reg (ν : ℝ) (a : CriticalSobolev 1) : Prop :=
  CriticalDatumAX6 ν a ∧ ∃ U : CriticalRegularSolution ν a,
    CriticalLerayHopf ν (criticalInitialPhysicalL2 a) U.lerayVelocity U.lerayGradient ∧
    U.lerayHopfUnique ∧
    PositiveSmoothNSE ν U.flow.velocity U.flow.pressure ∧
    (MemLp U.flow.threeHalfState 2 (volume.restrict (Ioi (0 : ℝ))) ∧
      (∫ t in Ioi (0 : ℝ), ‖U.flow.threeHalfState t‖ ^ 2) ≤ criticalDissipationBudget ν a) ∧
    (MemLp U.flow.negativeHalfDerivative 2 (volume.restrict (Ioi (0 : ℝ))) ∧
      (∫ t in Ioi (0 : ℝ), ‖U.flow.negativeHalfDerivative t‖ ^ 2) ≤
        criticalTimeDerivativeBudget ν a) ∧
    MemLp (fun t => criticalSpatialNorm 6 (U.flow.velocity t)) 4
      (volume.restrict (Ioi (0 : ℝ))) ∧
    (∀ T : ℝ, 0 < T →
      IntegrableOn (fun t => physicalDissipation (U.flow.velocity t) ^ 2)
        (Icc (0 : ℝ) T) volume ∧
      (∫ t in (0 : ℝ)..T, physicalDissipation (U.flow.velocity t) ^ 2) ≤
        (‖a‖ ^ 4 - ‖U.critical T‖ ^ 4) /
          (4 * (ν - criticalNonlinearConstant * ‖a‖)))

theorem NATIVE_ENERGY_REALIZATION (a : CriticalSobolev 1) (ha : CriticalSigmaZero a) :
    (‖a‖ ^ 2 = ∑' ki : FourierIndex,
      criticalFrequencyWeight ki.1 * Complex.normSq (criticalCoeff 1 a ki.1 ki.2)) ∧
    (‖physicalL2 a‖ ^ 2 = ∑' ki : FourierIndex,
      Complex.normSq (criticalCoeff 1 a ki.1 ki.2)) ∧
    datumFourierCoeff (physicalL2 a : Field) = criticalCoeff 1 a := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [zpow_one] using criticalSobolev_norm_sq 1 a
  · exact criticalInitialPhysicalL2_norm_sq a ha.reality ha.mean_zero
  · exact criticalInitialPhysicalL2_fourierCoeff a ha.reality ha.mean_zero

theorem frequencyWeight_ge_two_pi (k : Frequency) (hk : k ≠ 0) :
    2 * Real.pi ≤ criticalFrequencyWeight k := by
  have hk1 : (1 : ℝ) ≤ (galerkinFreqSq k : ℝ) := by
    exact_mod_cast galerkinFreqSq_ge_one_of_ne_zero k hk
  have hsq := criticalFrequencyWeight_sq_of_ne_zero k hk
  have hpos := criticalFrequencyWeight_pos k
  have hpi := Real.pi_pos
  change criticalFrequencyWeight k ^ 2 =
    (2 * Real.pi) ^ 2 * (galerkinFreqSq k : ℝ) at hsq
  have hmul := mul_le_mul_of_nonneg_left hk1 (sq_nonneg (2 * Real.pi))
  nlinarith

theorem physical_frequency_gap (a : CriticalSobolev 1) (ha : CriticalSigmaZero a) :
    (2 * Real.pi) * ‖physicalL2 a‖ ^ 2 ≤ ‖a‖ ^ 2 := by
  let b := criticalSobolevLower 0 1 (by norm_num) a
  have hmono : ‖(Real.sqrt (2 * Real.pi) : ℂ) • criticalSobolevRepr 0 b‖ ≤
      ‖criticalSobolevRepr 1 a‖ := by
    apply lp.norm_mono (by norm_num)
    intro ki
    change ‖(Real.sqrt (2 * Real.pi) : ℂ) *
        criticalWeightedCoeff 0 (criticalCoeff 0 b) ki‖ ≤
      ‖criticalWeightedCoeff 1 (criticalCoeff 1 a) ki‖
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), criticalWeightedCoeff_norm,
      criticalWeightedCoeff_norm]
    dsimp only [b]
    rw [criticalSobolevLower_coeff]
    simp only [zpow_zero, zpow_one, one_mul]
    by_cases hk : ki.1 = 0
    · simp only [hk, ha.mean_zero ki.2, norm_zero, mul_zero, le_refl]
    · apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact Real.sqrt_le_sqrt (frequencyWeight_ge_two_pi ki.1 hk)
  have hn : Real.sqrt (2 * Real.pi) * ‖physicalL2 a‖ ≤ ‖a‖ := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _),
      (criticalSobolevRepr 0).norm_map, (criticalSobolevRepr 1).norm_map] at hmono
    rw [physicalL2_eq_native, criticalInitialPhysicalL2_norm a ha.reality ha.mean_zero]
    exact hmono
  calc
    (2 * Real.pi) * ‖physicalL2 a‖ ^ 2 =
        (Real.sqrt (2 * Real.pi) * ‖physicalL2 a‖) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 2 * Real.pi)]
    _ ≤ ‖a‖ ^ 2 := (sq_le_sq₀ (by positivity) (norm_nonneg a)).mpr hn

theorem calibrationGamma_pos : 0 < calibrationGamma := by
  have hpi := Real.pi_gt_three
  have hden : 0 < 4 * Real.pi := by positivity
  have hquot : (5 : ℝ) / (4 * Real.pi) < 1 := by
    apply (div_lt_iff₀ hden).2
    linarith
  dsimp [calibrationGamma]
  linarith

theorem calibrationCap_pos : 0 < calibrationCap := by
  apply lt_min Real.pi_pos
  exact div_pos calibrationGamma_pos
    (mul_pos (by norm_num) (sq_pos_of_pos criticalNonlinearConstant_pos))

theorem SHIFTED_ENERGY_COERCIVITY
    (ν : ℝ) (hν : 0 < ν) (a : CriticalSobolev 1) (ha : CriticalSigmaZero a) :
    calibrationGamma * ‖a‖ ^ 2 ≤ 2 * ν ^ 2 * shiftedEnergy ν a ∧
    2 * ν ^ 2 * shiftedEnergy ν a ≤ ‖a‖ ^ 2 := by
  have hν2 : 2 * ν ^ 2 ≠ 0 := by positivity
  have hid : 2 * ν ^ 2 * shiftedEnergy ν a =
      ‖a‖ ^ 2 - (5 / 2 : ℝ) * ‖physicalL2 a‖ ^ 2 := by
    unfold shiftedEnergy
    field_simp [hν.ne']
  rw [hid]
  have hgap := physical_frequency_gap a ha
  have hratio : ‖physicalL2 a‖ ^ 2 ≤ ‖a‖ ^ 2 / (2 * Real.pi) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * Real.pi)).2
    nlinarith only [hgap]
  have hscale := mul_le_mul_of_nonneg_left hratio (by norm_num : (0 : ℝ) ≤ 5 / 2)
  constructor
  · calc
      calibrationGamma * ‖a‖ ^ 2 =
          ‖a‖ ^ 2 - (5 / 2 : ℝ) * (‖a‖ ^ 2 / (2 * Real.pi)) := by
            unfold calibrationGamma
            ring
      _ ≤ ‖a‖ ^ 2 - (5 / 2 : ℝ) * ‖physicalL2 a‖ ^ 2 := sub_le_sub_left hscale _
  · nlinarith [sq_nonneg ‖physicalL2 a‖]

theorem shiftedEnergy_nonneg
    (ν : ℝ) (hν : 0 < ν) (a : CriticalSobolev 1) (ha : CriticalSigmaZero a) :
    0 ≤ shiftedEnergy ν a := by
  have h := (SHIFTED_ENERGY_COERCIVITY ν hν a ha).1
  have hleft := mul_nonneg calibrationGamma_pos.le (sq_nonneg ‖a‖)
  have hν2 : 0 < 2 * ν ^ 2 := by positivity
  exact (mul_nonneg_iff_of_pos_left hν2).mp (hleft.trans h)

theorem calibratedScore_nonneg
    (ν : ℝ) (hν : 0 < ν) (a : CriticalSobolev 1) (ha : CriticalSigmaZero a) :
    0 ≤ calibratedScore ν a :=
  mul_nonneg (div_nonneg Real.pi_pos.le calibrationCap_pos.le)
    (shiftedEnergy_nonneg ν hν a ha)

theorem stageZeroBudget_eq_two_lt_pi : stageZeroBudget = 2 ∧ stageZeroBudget < Real.pi := by
  constructor
  · rfl
  · dsimp [stageZeroBudget]
    linarith [Real.pi_gt_three]

theorem FIRST_STAGE_IMPLIES_NATIVE_SMALL
    (ν : ℝ) (hν : 0 < ν) (a : CriticalSobolev 1) (ha : CriticalSigmaZero a)
    (hscore : calibratedScore ν a < 2) :
    criticalNonlinearConstant * ‖a‖ < ν := by
  have hC := criticalNonlinearConstant_pos
  have hγ := calibrationGamma_pos
  have hκ := calibrationCap_pos
  have hπ := Real.pi_pos
  have hscorePi : calibratedScore ν a < Real.pi :=
    hscore.trans (by linarith [Real.pi_gt_three])
  have hAcap : shiftedEnergy ν a < calibrationCap := by
    unfold calibratedScore at hscorePi
    have h := mul_lt_mul_of_pos_right hscorePi hκ
    have hcancel : (Real.pi / calibrationCap * shiftedEnergy ν a) * calibrationCap =
        Real.pi * shiftedEnergy ν a := by
      field_simp [calibrationCap_pos.ne']
    rw [hcancel] at h
    have h' := mul_lt_mul_of_pos_left h (inv_pos.mpr hπ)
    simpa only [← mul_assoc, inv_mul_cancel₀ hπ.ne', one_mul] using h'
  have hcoerce := (SHIFTED_ENERGY_COERCIVITY ν hν a ha).1
  have hcap : calibrationCap ≤ calibrationGamma / (4 * criticalNonlinearConstant ^ 2) :=
    min_le_right _ _
  have hcapMul : calibrationCap * (4 * criticalNonlinearConstant ^ 2) ≤ calibrationGamma :=
    (le_div_iff₀ (by positivity : 0 < 4 * criticalNonlinearConstant ^ 2)).mp hcap
  have hstrict : calibrationGamma * ‖a‖ ^ 2 < 2 * ν ^ 2 * calibrationCap :=
    hcoerce.trans_lt (mul_lt_mul_of_pos_left hAcap (by positivity))
  have hm := mul_lt_mul_of_pos_left hstrict
    (show 0 < 4 * criticalNonlinearConstant ^ 2 by positivity)
  have hmcap := mul_le_mul_of_nonneg_left hcapMul (show 0 ≤ 2 * ν ^ 2 by positivity)
  have hγmul : calibrationGamma * (4 * criticalNonlinearConstant ^ 2 * ‖a‖ ^ 2) <
      calibrationGamma * (2 * ν ^ 2) := by
    nlinarith only [hm, hmcap]
  have hcancel : 4 * criticalNonlinearConstant ^ 2 * ‖a‖ ^ 2 < 2 * ν ^ 2 := by
    have h' := mul_lt_mul_of_pos_left hγmul (inv_pos.mpr hγ)
    simpa only [← mul_assoc, inv_mul_cancel₀ hγ.ne', one_mul] using h'
  have hsquare : (criticalNonlinearConstant * ‖a‖) ^ 2 < ν ^ 2 := by
    nlinarith only [hcancel, sq_nonneg (criticalNonlinearConstant * ‖a‖)]
  exact (sq_lt_sq₀ (mul_nonneg hC.le (norm_nonneg a)) hν.le).mp hsquare

theorem ADMISSION_IMPLIES_REGULARITY
    (ν : ℝ) (hν : 0 < ν) (a : CriticalSobolev 1) (ha : CriticalSigmaZero a)
    (hscore : calibratedScore ν a < 2) : Reg ν a :=
  NSE_H12_SIGMA_ZERO_SMALL_UNCONDITIONAL ν hν a ha
    (FIRST_STAGE_IMPLIES_NATIVE_SMALL ν hν a ha hscore)

end
end SingularityDisprovement
