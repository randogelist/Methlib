import SingularityDisprovement.Admission
import Mathlib.MeasureTheory.Function.EssSup
import Mathlib.Analysis.SpecificLimits.Basic

/-! Positive scaling on the actual native carrier, positive-measure essential
unboundedness, and an elementary dyadic admission scale. -/

set_option autoImplicit false
set_option Elab.async true

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal

namespace SingularityDisprovement
open SingularClosure
noncomputable section

theorem criticalCoeff_real_smul (r : ℝ) (a : CriticalSobolev 1)
    (k : Frequency) (i : Fin 3) :
    criticalCoeff 1 (r • a) k i = (r : ℂ) * criticalCoeff 1 a k i := by
  change criticalCoeff 1 ((r : ℂ) • a) k i = _
  rw [criticalCoeff_smul]
  rfl

theorem sigma_real_smul (r : ℝ) (a : CriticalSobolev 1)
    (ha : CriticalSigmaZero a) : CriticalSigmaZero (r • a) := by
  constructor
  · intro k i
    rw [criticalCoeff_real_smul, criticalCoeff_real_smul, ha.reality k i]
    simp
  · intro k
    change (∑ i : Fin 3, (k i : ℂ) * criticalCoeff 1 (r • a) k i) = 0
    simp only [criticalCoeff_real_smul]
    calc
      _ = (r : ℂ) * ∑ i : Fin 3, (k i : ℂ) * criticalCoeff 1 a k i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = 0 := by rw [ha.solenoidal k, mul_zero]
  · intro i
    rw [criticalCoeff_real_smul, ha.mean_zero i, mul_zero]

theorem critical_norm_smul_pos (r : ℝ) (hr : 0 < r) (a : CriticalSobolev 1) :
    ‖r • a‖ = r * ‖a‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]

theorem physical_norm_smul_pos (r : ℝ) (hr : 0 < r) (a : CriticalSobolev 1) :
    ‖physicalL2 (r • a)‖ = r * ‖physicalL2 a‖ := by
  rw [physicalL2_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hr]

theorem shiftedEnergy_smul_pos (ν r : ℝ) (hr : 0 < r) (a : CriticalSobolev 1) :
    shiftedEnergy ν (r • a) = r ^ 2 * shiftedEnergy ν a := by
  unfold shiftedEnergy
  rw [critical_norm_smul_pos r hr, physical_norm_smul_pos r hr]
  ring

theorem calibratedScore_smul_pos (ν r : ℝ) (hr : 0 < r)
    (a : CriticalSobolev 1) :
    calibratedScore ν (r • a) = r ^ 2 * calibratedScore ν a := by
  unfold calibratedScore
  rw [shiftedEnergy_smul_pos ν r hr]
  ring

theorem kineticDensity_smul_ae (r : ℝ) (hr : 0 < r) (a : CriticalSobolev 1) :
    kineticDensity (r • a) =ᵐ[volume.restrict unitCube]
      fun x => r ^ 2 * kineticDensity a x := by
  have hfn : (physicalL2 (r • a) : Field) =ᵐ[volume.restrict unitCube]
      fun x => r • physicalL2 a x := by
    rw [physicalL2_smul]
    exact Lp.coeFn_smul r (physicalL2 a)
  filter_upwards [hfn] with x hx
  simp only [kineticDensity, hx, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
  ring

theorem EssUnbounded.smul {a : CriticalSobolev 1} (ha : EssUnbounded a)
    (r : ℝ) (hr : 0 < r) : EssUnbounded (r • a) := by
  intro M hM
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
  apply lt_of_lt_of_le (ha (M / r ^ 2) (div_nonneg hM hr2.le))
  apply measure_mono_ae
  filter_upwards [kineticDensity_smul_ae r hr a] with x hx
  intro hlevel
  change M < kineticDensity (r • a) x
  rw [hx]
  have h := (div_lt_iff₀ hr2).mp hlevel
  simpa only [mul_comm] using h

def densityEssSup (a : CriticalSobolev 1) : ℝ≥0∞ :=
  essSup (fun x => ENNReal.ofReal (kineticDensity a x)) (volume.restrict unitCube)

theorem essUnbounded_iff_densityEssSup_eq_top (a : CriticalSobolev 1) :
    EssUnbounded a ↔ densityEssSup a = ⊤ := by
  constructor
  · intro ha
    unfold densityEssSup
    rw [essSup_eq_sInf]
    apply le_antisymm le_top
    apply le_sInf
    intro b hb
    change (volume.restrict unitCube)
      {x | b < ENNReal.ofReal (kineticDensity a x)} = 0 at hb
    by_cases hbtop : b = ⊤
    · simp [hbtop]
    · have hp := ha b.toReal ENNReal.toReal_nonneg
      have hs : {x | b < ENNReal.ofReal (kineticDensity a x)} =
          {x | b.toReal < kineticDensity a x} := by
        ext x
        exact ENNReal.lt_ofReal_iff_toReal_lt hbtop
      rw [hs] at hb
      exact False.elim ((ne_of_gt hp) hb)
  · intro ha M hM
    by_contra hn
    have hz : (volume.restrict unitCube) {x | M < kineticDensity a x} = 0 :=
      le_antisymm (le_of_not_gt hn) bot_le
    have hreal : ∀ᵐ x ∂volume.restrict unitCube, kineticDensity a x ≤ M := by
      rw [ae_iff]
      simpa only [not_le] using hz
    have hbound : ∀ᵐ x ∂volume.restrict unitCube,
        ENNReal.ofReal (kineticDensity a x) ≤ ENNReal.ofReal M := by
      filter_upwards [hreal] with x hx
      exact ENNReal.ofReal_le_ofReal hx
    have hsup := essSup_le_of_ae_le (ENNReal.ofReal M) hbound
    change densityEssSup a ≤ ENNReal.ofReal M at hsup
    rw [ha] at hsup
    exact ENNReal.ofReal_ne_top (top_le_iff.mp hsup)

theorem POSITIVE_SCALING_LAWS (ν r : ℝ) (hr : 0 < r)
    (a : CriticalSobolev 1) (ha : CriticalSigmaZero a) :
    CriticalSigmaZero (r • a) ∧
    ‖r • a‖ = r * ‖a‖ ∧
    ‖physicalL2 (r • a)‖ = r * ‖physicalL2 a‖ ∧
    calibratedScore ν (r • a) = r ^ 2 * calibratedScore ν a ∧
    (kineticDensity (r • a) =ᵐ[volume.restrict unitCube]
      fun x => r ^ 2 * kineticDensity a x) ∧
    (EssUnbounded a → EssUnbounded (r • a)) ∧
    (EssUnbounded a ↔ densityEssSup a = ⊤) := by
  exact ⟨sigma_real_smul r a ha, critical_norm_smul_pos r hr a,
    physical_norm_smul_pos r hr a, calibratedScore_smul_pos ν r hr a,
    kineticDensity_smul_ae r hr a, (fun h => h.smul r hr),
    essUnbounded_iff_densityEssSup_eq_top a⟩

/-- The scale is dyadic; no computable numerical value for C is assumed. -/
theorem SMALL_POSITIVE_DYADIC_SCALE_EXISTS (ν ε : ℝ) (hν : 0 < ν) (hε : 0 < ε)
    (b : CriticalSobolev 1) (hb : CriticalSigmaZero b) (hbpos : 0 < ‖b‖) :
    ∃ m : ℕ, 1 ≤ m ∧
      0 < ‖((1 / 2 : ℝ) ^ m) • b‖ ∧
      ‖((1 / 2 : ℝ) ^ m) • b‖ < ε ∧
      calibratedScore ν (((1 / 2 : ℝ) ^ m) • b) < 1 := by
  let s : ℝ := calibratedScore ν b
  have hs : 0 ≤ s := calibratedScore_nonneg ν hν b hb
  have hs1 : 0 < 1 + s := by linarith
  have hroot : 0 < Real.sqrt (1 + s) := Real.sqrt_pos.mpr hs1
  let δ : ℝ := min (1 / 2) (min (ε / (2 * (1 + ‖b‖))) (1 / Real.sqrt (1 + s)))
  have hδ : 0 < δ := by
    dsimp only [δ]
    exact lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hδ (by norm_num : (1 / 2 : ℝ) < 1)
  have hmpos : 1 ≤ m := by
    apply Nat.one_le_iff_ne_zero.mpr
    intro hmzero
    subst m
    have hδhalf : δ ≤ (1 / 2 : ℝ) := min_le_left _ _
    have hmone : (1 : ℝ) < δ := by simpa only [pow_zero] using hm
    linarith
  let r : ℝ := (1 / 2 : ℝ) ^ m
  have hr : 0 < r := pow_pos (by norm_num) _
  have hrnorm : r ≤ ε / (2 * (1 + ‖b‖)) :=
    hm.le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrscore : r ≤ 1 / Real.sqrt (1 + s) :=
    hm.le.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hnormmul := (le_div_iff₀ (by positivity : 0 < 2 * (1 + ‖b‖))).mp hrnorm
  have hnormlt : r * ‖b‖ < ε := by nlinarith [norm_nonneg b]
  have hscoremul := (le_div_iff₀ hroot).mp hrscore
  have hmulnonneg : 0 ≤ r * Real.sqrt (1 + s) := mul_nonneg hr.le hroot.le
  have hsq : (r * Real.sqrt (1 + s)) ^ 2 ≤ 1 := by
    simpa only [one_pow] using
      (sq_le_sq₀ hmulnonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr hscoremul
  rw [mul_pow, Real.sq_sqrt hs1.le] at hsq
  have hscorelt : r ^ 2 * s < 1 := by nlinarith [sq_pos_of_pos hr]
  refine ⟨m, hmpos, ?_, ?_, ?_⟩
  · rw [critical_norm_smul_pos r hr b]
    exact mul_pos hr hbpos
  · rw [critical_norm_smul_pos r hr b]
    exact hnormlt
  · rw [calibratedScore_smul_pos ν r hr b]
    exact hscorelt

end
end SingularityDisprovement
