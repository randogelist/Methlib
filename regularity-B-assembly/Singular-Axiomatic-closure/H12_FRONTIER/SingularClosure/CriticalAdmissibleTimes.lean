import Mathlib

/-! Positive admissible times approaching the initial time, extracted from
an almost-everywhere predicate on a genuine Lebesgue interval. -/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory Filter
open scoped Topology

namespace SingularClosure

/-- Every predicate holding almost everywhere on `(0,T]` admits positive
times approaching zero at which the predicate holds. -/
theorem CRITICAL_ADMISSIBLE_TIMES_TENDSTO_ZERO
    {T : ℝ} (hT : 0 < T) (P : ℝ → Prop)
    (hP : ∀ᵐ s ∂volume.restrict (Ioc (0 : ℝ) T), P s) :
    ∃ ε : ℕ → ℝ,
      (∀ n, ε n ∈ Ioc (0 : ℝ) T ∧ P (ε n)) ∧
      Tendsto ε atTop (𝓝 0) := by
  classical
  have hex (n : ℕ) :
      ∃ s : ℝ, s ∈ Ioc (0 : ℝ) (min T (1 / ((n : ℝ) + 1))) ∧ P s := by
    have hpos : 0 < min T (1 / ((n : ℝ) + 1)) :=
      lt_min hT (by positivity)
    have hsub : Ioc (0 : ℝ) (min T (1 / ((n : ℝ) + 1))) ⊆ Ioc (0 : ℝ) T := by
      intro s hs
      exact ⟨hs.1, hs.2.trans (min_le_left _ _)⟩
    have hm : volume (Ioc (0 : ℝ) (min T (1 / ((n : ℝ) + 1)))) ≠ 0 := by
      rw [Real.volume_Ioc, sub_zero]
      exact ne_of_gt (ENNReal.ofReal_pos.mpr hpos)
    exact Measure.exists_mem_of_measure_ne_zero_of_ae hm
      (ae_restrict_of_ae_restrict_of_subset hsub hP)
  choose ε hε using hex
  refine ⟨ε, ?_, ?_⟩
  · intro n
    exact ⟨⟨(hε n).1.1, (hε n).1.2.trans (min_le_left _ _)⟩, (hε n).2⟩
  · exact squeeze_zero (fun n => (hε n).1.1.le)
      (fun n => (hε n).1.2.trans (min_le_right _ _))
      tendsto_one_div_add_atTop_nhds_zero_nat

end SingularClosure
