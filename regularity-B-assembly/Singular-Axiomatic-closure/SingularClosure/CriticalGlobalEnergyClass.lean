import SingularClosure.SmallDataQuantitative
import SingularClosure.CriticalGlobalLp

/-! Canonical global Bochner representatives of the actual positive flow.
The H3/2 representative and the H-1/2 time derivative are obtained from
bounded coefficient-preserving maps, and their global budgets follow
from the proved quantitative local representatives. -/

set_option autoImplicit false
set_option Elab.async true
open Set MeasureTheory Filter
open scoped Topology Interval ENNReal

namespace SingularClosure
noncomputable section

theorem critical_three_weight_le_torus_two (c : FourierCoeff) (ki : FourierIndex) :
    ‖criticalWeightedCoeff 3 c ki‖ ≤ ‖sobolevWeightedCoeff 2 c ki‖ := by
  calc
    _ ≤ ‖criticalWeightedCoeff 4 c ki‖ :=
      criticalWeightedCoeff_norm_mono (by norm_num) c ki
    _ = criticalFrequencyWeight ki.1 ^ 2 * ‖c ki.1 ki.2‖ := by
      rw [criticalWeightedCoeff_norm, zpow_ofNat,
        show criticalHalfWeight ki.1 ^ 4 = (criticalHalfWeight ki.1 ^ 2) ^ 2 by ring,
        criticalHalfWeight_sq]
    _ ≤ torusSobolevWeight ki.1 ^ 2 * ‖c ki.1 ki.2‖ :=
      mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (criticalFrequencyWeight_pos ki.1).le
          (criticalFrequencyWeight_le_torusSobolevWeight ki.1) 2) (norm_nonneg _)
    _ = ‖sobolevWeightedCoeff 2 c ki‖ := by
      simp only [sobolevWeightedCoeff, norm_mul, norm_pow, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (torusSobolevWeight_pos ki.1)]

def criticalFromTorusTwoLinear : TorusSobolev 2 →ₗ[ℂ] CriticalSobolev 3 where
  toFun c := ⟨c.val, c.property.mono' (critical_three_weight_le_torus_two c.val)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem criticalFromTorusTwoLinear_coeff (c : TorusSobolev 2) :
    criticalCoeff 3 (criticalFromTorusTwoLinear c) = c.val := rfl

theorem criticalFromTorusTwoLinear_norm_le (c : TorusSobolev 2) :
    ‖criticalFromTorusTwoLinear c‖ ≤ ‖c‖ := by
  calc
    _ = ‖criticalSobolevRepr 3 (criticalFromTorusTwoLinear c)‖ :=
      ((criticalSobolevRepr 3).norm_map _).symm
    _ ≤ ‖torusSobolevRepr 2 c‖ := by
      apply lp.norm_mono (by norm_num)
      intro ki
      change ‖criticalWeightedCoeff 3 c.val ki‖ ≤ ‖sobolevWeightedCoeff 2 c.val ki‖
      exact critical_three_weight_le_torus_two c.val ki
    _ = ‖c‖ := (torusSobolevRepr 2).norm_map c

def criticalFromTorusTwo : TorusSobolev 2 →L[ℂ] CriticalSobolev 3 :=
  criticalFromTorusTwoLinear.mkContinuous 1
    (fun c => by simpa only [one_mul] using criticalFromTorusTwoLinear_norm_le c)

@[simp]
theorem criticalFromTorusTwo_coeff (c : TorusSobolev 2) :
    criticalCoeff 3 (criticalFromTorusTwo c) = c.val := rfl

def criticalNegativeFromTorusZero : TorusSobolev 0 →L[ℂ] CriticalSobolev (-1) :=
  (criticalSobolevLower (-1) 0 (by norm_num)).comp
    criticalH0Equiv.symm.toContinuousLinearEquiv.toContinuousLinearMap

@[simp]
theorem criticalNegativeFromTorusZero_coeff (c : TorusSobolev 0) :
    criticalCoeff (-1) (criticalNegativeFromTorusZero c) = c.val := by
  change criticalCoeff (-1)
    (criticalSobolevLower (-1) 0 (by norm_num) (criticalH0Equiv.symm c)) = _
  rw [criticalSobolevLower_coeff]
  have h := criticalH0Equiv_coeff (criticalH0Equiv.symm c)
  rw [criticalH0Equiv.apply_symm_apply] at h
  exact h.symm

def CriticalPositiveSobolevFlow.threeHalfState
    {ν : ℝ} (L : CriticalPositiveSobolevFlow ν) (t : ℝ) : CriticalSobolev 3 :=
  if 0 < t then criticalFromTorusTwo (L.state 2 t) else 0

def CriticalPositiveSobolevFlow.negativeHalfDerivative
    {ν : ℝ} (L : CriticalPositiveSobolevFlow ν) (t : ℝ) : CriticalSobolev (-1) :=
  if 0 < t then
    criticalNegativeFromTorusZero (fourierSobolevRhs ν 0 (L.state 2 t)) else 0

theorem CriticalPositiveSobolevFlow.threeHalfState_coeff
    {ν : ℝ} (L : CriticalPositiveSobolevFlow ν) (t : ℝ) (ht : 0 < t) :
    criticalCoeff 3 (L.threeHalfState t) = (L.state 0 t).val := by
  rw [CriticalPositiveSobolevFlow.threeHalfState, if_pos ht, criticalFromTorusTwo_coeff]
  exact L.coeff 2 t ht

theorem CriticalPositiveSobolevFlow.threeHalfState_physical_coeff
    {ν : ℝ} (L : CriticalPositiveSobolevFlow ν) (t : ℝ) (ht : 0 < t) :
    criticalCoeff 3 (L.threeHalfState t) = datumFourierCoeff (L.velocity t) := by
  rw [L.threeHalfState_coeff t ht]
  exact (datumFourierCoeff_smoothFourierSynthesis (L.state 0 t).val
    (ALL_SOBOLEV_IMP_RAPID_SCALAR _ (L.state_all_mem t ht)) (L.reality t ht)).symm

theorem CriticalPositiveSobolevFlow.negativeHalfDerivative_coeff
    {ν : ℝ} (L : CriticalPositiveSobolevFlow ν) (t : ℝ) (ht : 0 < t) :
    criticalCoeff (-1) (L.negativeHalfDerivative t) =
      datumFourierCoeff (timeDerivative L.velocity t) := by
  rw [CriticalPositiveSobolevFlow.negativeHalfDerivative, if_pos ht,
    criticalNegativeFromTorusZero_coeff, L.rhs_coeff 0 t ht,
    L.timeDerivative_fourierCoeff t ht]

theorem CriticalPositiveSobolevFlow.threeHalfState_continuousOn
    {ν : ℝ} (L : CriticalPositiveSobolevFlow ν) :
    ContinuousOn L.threeHalfState (Ioi 0) := by
  apply (criticalFromTorusTwo.continuous.comp_continuousOn (L.continuous 2)).congr
  intro t ht
  simp only [CriticalPositiveSobolevFlow.threeHalfState, if_pos ht]

theorem CriticalPositiveSobolevFlow.negativeHalfDerivative_continuousOn
    {ν : ℝ} (L : CriticalPositiveSobolevFlow ν) :
    ContinuousOn L.negativeHalfDerivative (Ioi 0) := by
  apply (criticalNegativeFromTorusZero.continuous.comp_continuousOn
    ((fourierSobolevRhs_contDiff ν 0).continuous.comp_continuousOn (L.continuous 2))).congr
  intro t ht
  simp only [CriticalPositiveSobolevFlow.negativeHalfDerivative, if_pos ht]

/-- Uniform quantitative local representatives determine canonical global
Bochner fields with the same literal Fourier coefficients. -/
theorem CriticalRegularSolution.global_energy_class
    {ν : ℝ} {a : CriticalSobolev 1} (U : CriticalRegularSolution ν a)
    (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hW : ∀ T : ℝ, 0 < T → ∃ W : ℝ → CriticalSobolev 3,
      MemLp W 2 (volume.restrict (Icc (0 : ℝ) T)) ∧
      (∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T),
        criticalCoeff 3 (W t) = criticalCoeff 1 (U.critical t)) ∧
      (∫ t in Icc (0 : ℝ) T, ‖W t‖ ^ 2) ≤ B)
    (hV : ∀ T : ℝ, 0 < T → ∃ V : ℝ → CriticalSobolev (-1),
      MemLp V 2 (volume.restrict (Icc (0 : ℝ) T)) ∧
      (∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T),
        criticalCoeff (-1) (V t) = datumFourierCoeff (timeDerivative U.flow.velocity t)) ∧
      (∫ t in Icc (0 : ℝ) T, ‖V t‖ ^ 2) ≤ D) :
    (MemLp U.flow.threeHalfState 2 (volume.restrict (Ioi (0 : ℝ))) ∧
      (∫ t in Ioi (0 : ℝ), ‖U.flow.threeHalfState t‖ ^ 2) ≤ B) ∧
    (MemLp U.flow.negativeHalfDerivative 2 (volume.restrict (Ioi (0 : ℝ))) ∧
      (∫ t in Ioi (0 : ℝ), ‖U.flow.negativeHalfDerivative t‖ ^ 2) ≤ D) := by
  constructor
  · apply critical_global_L2_of_uniform_local U.flow.threeHalfState B hB
    intro T hT
    obtain ⟨W, hWmem, hWcoeff, hWbound⟩ := hW T hT
    have heq : W =ᵐ[volume.restrict (Icc (0 : ℝ) T)] U.flow.threeHalfState := by
      filter_upwards [hWcoeff, critical_ae_positive_on_Icc T] with t hWt ht
      apply criticalCoeff_injective 3
      rw [U.flow.threeHalfState_coeff t ht, U.coefficient_agreement t ht]
      exact hWt
    refine ⟨(memLp_congr_ae heq).mp hWmem, ?_⟩
    have hi : (∫ t in Icc (0 : ℝ) T, ‖W t‖ ^ 2) =
        ∫ t in Icc (0 : ℝ) T, ‖U.flow.threeHalfState t‖ ^ 2 :=
      integral_congr_ae (heq.mono (fun _ h => by rw [h]))
    exact hi ▸ hWbound
  · apply critical_global_L2_of_uniform_local U.flow.negativeHalfDerivative D hD
    intro T hT
    obtain ⟨V, hVmem, hVcoeff, hVbound⟩ := hV T hT
    have heq : V =ᵐ[volume.restrict (Icc (0 : ℝ) T)] U.flow.negativeHalfDerivative := by
      filter_upwards [hVcoeff, critical_ae_positive_on_Icc T] with t hVt ht
      apply criticalCoeff_injective (-1)
      rw [U.flow.negativeHalfDerivative_coeff t ht]
      exact hVt
    refine ⟨(memLp_congr_ae heq).mp hVmem, ?_⟩
    have hi : (∫ t in Icc (0 : ℝ) T, ‖V t‖ ^ 2) =
        ∫ t in Icc (0 : ℝ) T, ‖U.flow.negativeHalfDerivative t‖ ^ 2 :=
      integral_congr_ae (heq.mono (fun _ h => by rw [h]))
    exact hi ▸ hVbound

theorem SMALL_DATA_CRITICAL_GLOBAL_ENERGY_CLASS
    (ν : ℝ) (hν : 0 < ν) (a : CriticalSobolev 1) (ha : CriticalSigmaZero a)
    (hsmall : criticalNonlinearConstant * ‖a‖ < ν) :
    ∃ U : CriticalRegularSolution ν a,
      (MemLp U.flow.threeHalfState 2 (volume.restrict (Ioi (0 : ℝ))) ∧
        (∫ t in Ioi (0 : ℝ), ‖U.flow.threeHalfState t‖ ^ 2) ≤ criticalDissipationBudget ν a) ∧
      (MemLp U.flow.negativeHalfDerivative 2 (volume.restrict (Ioi (0 : ℝ))) ∧
        (∫ t in Ioi (0 : ℝ), ‖U.flow.negativeHalfDerivative t‖ ^ 2) ≤
          criticalTimeDerivativeBudget ν a) ∧
      (∀ T : ℝ, 0 < T →
        IntegrableOn (fun t => physicalDissipation (U.flow.velocity t) ^ 2)
          (Icc (0 : ℝ) T) volume ∧
        (∫ t in (0 : ℝ)..T, physicalDissipation (U.flow.velocity t) ^ 2) ≤
          (‖a‖ ^ 4 - ‖U.critical T‖ ^ 4) /
            (4 * (ν - criticalNonlinearConstant * ‖a‖))) := by
  obtain ⟨U, hW, hV, hquartic⟩ :=
    SMALL_DATA_CRITICAL_QUANTITATIVE_REGULARITY ν hν a ha hsmall
  obtain ⟨hWglobal, hVglobal⟩ := U.global_energy_class
    (criticalDissipationBudget ν a) (criticalTimeDerivativeBudget ν a)
    (criticalDissipationBudget_nonneg a hsmall)
    (criticalTimeDerivativeBudget_nonneg a hsmall) hW hV
  exact ⟨U, hWglobal, hVglobal, hquartic⟩

end
end SingularClosure
