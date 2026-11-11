import SingularClosure.CriticalHomogeneousL6

/-! Global time L4 follows from the uniform actual physical quartic budget. -/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory Filter
open scoped Topology Interval ENNReal

namespace SingularClosure
noncomputable section

theorem critical_halfline_fourth_budget
    (f : ℝ → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hf : AEStronglyMeasurable f (volume.restrict (Ioi (0 : ℝ))))
    (hloc : ∀ T : ℝ, 0 < T → IntegrableOn (fun t => f t ^ 4) (Ioc (0 : ℝ) T) volume)
    (hbudget : ∀ T : ℝ, 0 < T → (∫ t in Ioc (0 : ℝ) T, f t ^ 4) ≤ B) :
    MemLp f 4 (volume.restrict (Ioi (0 : ℝ))) ∧
      (∫ t in Ioi (0 : ℝ), f t ^ 4) ≤ B := by
  have hf0 (t : ℝ) : 0 ≤ f t ^ 4 := by positivity
  let s : ℕ → Set ℝ := fun n => Ioc (0 : ℝ) ((n : ℝ) + 1)
  have hs : (⋃ n, s n) = Ioi (0 : ℝ) := by
    ext t
    constructor
    · intro ht
      obtain ⟨n, hn⟩ := mem_iUnion.mp ht
      exact hn.1
    · intro ht
      obtain ⟨n, hn⟩ := exists_nat_gt t
      exact mem_iUnion.mpr ⟨n, ht, by linarith⟩
  have hmono : Monotone s := by
    intro m n hmn
    apply Ioc_subset_Ioc_right
    exact add_le_add (by exact_mod_cast hmn) le_rfl
  have hlin : (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (f t ^ 4)) ≤ ENNReal.ofReal B := by
    rw [← hs, setLIntegral_iUnion_of_directed _ hmono.directed_le]
    apply iSup_le
    intro n
    have hn : 0 < (n : ℝ) + 1 := by positivity
    have heq := ofReal_integral_eq_lintegral_ofReal (hloc _ hn)
      (Filter.Eventually.of_forall hf0)
    rw [← heq]
    exact ENNReal.ofReal_le_ofReal (hbudget _ hn)
  have hi : Integrable (fun t => f t ^ 4) (volume.restrict (Ioi (0 : ℝ))) := by
    refine ⟨hf.pow 4, ?_⟩
    change (∫⁻ t in Ioi (0 : ℝ), ‖f t ^ 4‖ₑ) < ∞
    simpa only [Real.enorm_eq_ofReal (hf0 _)] using
      hlin.trans_lt ENNReal.ofReal_lt_top
  refine ⟨?_, ?_⟩
  · apply (integrable_norm_rpow_iff hf
      (by norm_num : (4 : ℝ≥0∞) ≠ 0) (by norm_num : (4 : ℝ≥0∞) ≠ ⊤)).mp
    have hpow (x : ℝ) : ‖x‖ ^ (4 : ℝ) = x ^ (4 : ℕ) := by
      rw [Real.rpow_ofNat, Real.norm_eq_abs]
      calc
        |x| ^ 4 = (|x| ^ 2) ^ 2 := by ring
        _ = (x ^ 2) ^ 2 := by rw [sq_abs]
        _ = x ^ 4 := by ring
    simpa only [ENNReal.toReal_ofNat, hpow] using hi
  · have heq := ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall hf0)
    rw [← heq] at hlin
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hlin
    rw [ENNReal.toReal_ofReal (integral_nonneg (fun t => by positivity)),
      ENNReal.toReal_ofReal hB] at h
    exact h

/-- Actual global Serrin membership and a universal physical L6 budget. -/
theorem CriticalRegularSolution.serrin_global_memLp_of_quartic_budget
    {ν : ℝ} {a : CriticalSobolev 1} (U : CriticalRegularSolution ν a)
    (M : ℝ) (hM : 0 ≤ M)
    (hquartic : ∀ T : ℝ, 0 < T →
      IntegrableOn (fun t => physicalDissipation (U.flow.velocity t) ^ 2)
        (Icc (0 : ℝ) T) volume ∧
      (∫ t in (0 : ℝ)..T, physicalDissipation (U.flow.velocity t) ^ 2) ≤ M) :
    MemLp (fun t => criticalSpatialNorm 6 (U.flow.velocity t)) 4
      (volume.restrict (Ioi (0 : ℝ))) ∧
      (∫ t in Ioi (0 : ℝ), criticalSpatialNorm 6 (U.flow.velocity t) ^ 4) ≤
        criticalPhysicalL6FourthConstant * M := by
  apply critical_halfline_fourth_budget _ (criticalPhysicalL6FourthConstant * M)
    (mul_nonneg criticalPhysicalL6FourthConstant_pos.le hM)
    (criticalPositive_spatialNorm_six_aestronglyMeasurable_Ioi U.flow)
  · intro T hT
    change Integrable (fun t => criticalSpatialNorm 6 (U.flow.velocity t) ^ 4)
      (volume.restrict (Ioc (0 : ℝ) T))
    have h := (U.serrin_time_memLp T (hquartic T hT).1).integrable_norm_pow
      (by norm_num : (4 : ℕ) ≠ 0)
    have hnorm (t : ℝ) : ‖criticalSpatialNorm 6 (U.flow.velocity t)‖ =
        criticalSpatialNorm 6 (U.flow.velocity t) :=
      Real.norm_of_nonneg (criticalSpatialNorm_nonneg 6 _)
    simpa only [hnorm] using h
  · intro T hT
    have h := (U.serrin_fourth_integral_le T hT.le (hquartic T hT).1).trans
      (mul_le_mul_of_nonneg_left (hquartic T hT).2 criticalPhysicalL6FourthConstant_pos.le)
    rw [intervalIntegral.integral_of_le hT.le] at h
    exact h

end
end SingularClosure
