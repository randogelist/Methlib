/-
Compact-support L1 translation continuity for the HVR Fourier route.
Adapted from the compact-support estimate in Mathlib's
Mathlib/Analysis/Fourier/RiemannLebesgueLemma.lean, Copyright 2022 David
Loeffler, Apache-2.0. The Riemann-Lebesgue file is not imported here.
This candidate has not yet been compiled or axiom-audited.
-/
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Tactic

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace HVRCompactTranslation

/-- Integral norm of a compactly supported continuous function's translation
    difference tends to zero at zero. -/
theorem translation_integral_tendsto (g : ℝ → ℂ) (hg : Continuous g)
    (hcompact : HasCompactSupport g) :
    Tendsto (fun h : ℝ => ∫ t : ℝ, ‖g (t + h) - g t‖) (𝓝 0) (𝓝 0) := by
  refine Metric.tendsto_nhds.mpr fun ε hε => ?_
  obtain ⟨R, -, hR_bd⟩ : ∃ R : ℝ, 0 < R ∧ ∀ t : ℝ, R ≤ ‖t‖ → g t = 0 :=
    hcompact.exists_pos_le_norm
  let A := {t : ℝ | ‖t‖ ≤ R + 1}
  have mA : MeasurableSet A := by
    suffices A = Metric.closedBall (0 : ℝ) (R + 1) by
      rw [this]
      exact Metric.isClosed_closedBall.measurableSet
    simp_rw [A, Metric.closedBall, dist_eq_norm, sub_zero]
  obtain ⟨B, hB_pos, hB_vol⟩ : ∃ B : ℝ≥0, 0 < B ∧ volume A ≤ B := by
    have hc : IsCompact A := by
      simpa only [Metric.closedBall, dist_eq_norm, sub_zero] using
        isCompact_closedBall (0 : ℝ) _
    let B₀ := volume A
    replace hc : B₀ < ⊤ := hc.measure_lt_top
    refine ⟨B₀.toNNReal + 1, add_pos_of_nonneg_of_pos B₀.toNNReal.coe_nonneg one_pos, ?_⟩
    rw [ENNReal.coe_add, ENNReal.coe_one, ENNReal.coe_toNNReal hc.ne]
    exact le_self_add
  have hB : (0 : ℝ) < B := NNReal.coe_pos.mpr hB_pos
  obtain ⟨δ, hδ, hδ_uc⟩ :=
    Metric.uniformContinuous_iff.mp (hcompact.uniformContinuous_of_continuous hg)
      (ε / (2 * (B : ℝ))) (by positivity)
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (lt_min hδ zero_lt_one)] with h hh
  have hh' : ‖h‖ < min δ 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hh
  have hhδ : ‖h‖ < δ := lt_of_lt_of_le hh' (min_le_left _ _)
  have hh1 : ‖h‖ < 1 := lt_of_lt_of_le hh' (min_le_right _ _)
  have int_A : (∫ t : ℝ, ‖g (t + h) - g t‖) =
      ∫ t in A, ‖g (t + h) - g t‖ := by
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht => ?_).symm
    dsimp only [A] at ht
    simp only [mem_ofPred, not_le] at ht
    have htn : R ≤ ‖t‖ := by linarith
    have hth : R ≤ ‖t + h‖ := by
      have hv : ‖t‖ - ‖h‖ ≤ ‖t + h‖ := by
        simpa using (norm_sub_norm_le t (-h))
      linarith
    rw [hR_bd (t + h) hth, hR_bd t htn]
    simp
  have bdA : ∀ t : ℝ, t ∈ A → ‖‖g (t + h) - g t‖‖ ≤ ε / (2 * (B : ℝ)) := by
    simp_rw [norm_norm]
    simp_rw [dist_eq_norm] at hδ_uc
    intro t _
    apply le_of_lt
    apply hδ_uc
    simpa [dist_eq_norm] using hhδ
  have bdA2 := norm_setIntegral_le_of_norm_le_const
    (hB_vol.trans_lt ENNReal.coe_lt_top) bdA
  have hint_nonneg : 0 ≤ ∫ t in A, ‖g (t + h) - g t‖ :=
    setIntegral_nonneg mA fun t _ => norm_nonneg _
  rw [Real.norm_of_nonneg hint_nonneg] at bdA2
  have hA : (volume A).toReal ≤ (B : ℝ) := by
    simpa using ENNReal.toReal_mono ENNReal.coe_ne_top hB_vol
  have hint_nonneg' : 0 ≤ ∫ t : ℝ, ‖g (t + h) - g t‖ :=
    integral_nonneg fun t => norm_nonneg _
  rw [dist_zero_right, Real.norm_of_nonneg hint_nonneg', int_A]
  calc
    (∫ t in A, ‖g (t + h) - g t‖) ≤
        (ε / (2 * (B : ℝ))) * (volume A).toReal := bdA2
    _ ≤ (ε / (2 * (B : ℝ))) * (B : ℝ) := by
      exact mul_le_mul_of_nonneg_left hA (by positivity)
    _ < ε := by
      field_simp [ne_of_gt hB] <;> nlinarith

end HVRCompactTranslation
