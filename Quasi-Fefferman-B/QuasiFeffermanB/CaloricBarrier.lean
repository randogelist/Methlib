import Mathlib

/-!
Continuous quadratic barriers used by the caloric Galerkin estimate.
All hypotheses concern scalar inequalities; no regularity conclusion is assumed.
-/

set_option autoImplicit false
set_option Elab.async true

open Set

namespace QuasiFeffermanB
noncomputable section

/-- A continuous scalar trajectory starting below a strict barrier cannot cross
that barrier while satisfying its quadratic estimate. -/
theorem CONTINUOUS_QUADRATIC_BARRIER
    (X : ℝ → ℝ) (h b R T : ℝ)
    (hcont : ContinuousOn X (Icc 0 T))
    (hzero : X 0 < R)
    (hbarrier : h + b * R ^ 2 < R)
    (hquad : ∀ t ∈ Icc (0 : ℝ) T, X t ≤ h + b * (X t) ^ 2) :
    ∀ t ∈ Icc (0 : ℝ) T, X t < R := by
  intro t ht
  by_contra hnot
  have hRt : R ≤ X t := le_of_not_gt hnot
  have hcont' : ContinuousOn X (Icc 0 t) :=
    hcont.mono (fun s hs => ⟨hs.1, hs.2.trans ht.2⟩)
  obtain ⟨s, hs, hXs⟩ :=
    intermediate_value_Icc ht.1 hcont' ⟨hzero.le, hRt⟩
  have hq := hquad s ⟨hs.1, hs.2.trans ht.2⟩
  rw [hXs] at hq
  exact (not_le_of_gt hbarrier) hq

/-- The positive heat-budget case gives the explicit bound X<2h. -/
theorem QUADRATIC_BARRIER_LT_TWO_HEAT_BUDGET
    (X : ℝ → ℝ) (h b T : ℝ) (hh : 0 < h)
    (hsmall : 4 * b * h < 1)
    (hcont : ContinuousOn X (Icc 0 T))
    (hzero : X 0 = 0)
    (hquad : ∀ t ∈ Icc (0 : ℝ) T, X t ≤ h + b * (X t) ^ 2) :
    ∀ t ∈ Icc (0 : ℝ) T, X t < 2 * h := by
  apply CONTINUOUS_QUADRATIC_BARRIER X h b (2 * h) T hcont
  · rw [hzero]
    positivity
  · have hm := mul_lt_mul_of_pos_right hsmall hh
    nlinarith
  · exact hquad

/-- A nonnegative continuous quadratic trajectory with zero heat budget is
identically zero. -/
theorem QUADRATIC_BARRIER_ZERO_HEAT_BUDGET
    (X : ℝ → ℝ) (b T : ℝ) (hb : 0 < b)
    (hcont : ContinuousOn X (Icc 0 T))
    (hzero : X 0 = 0)
    (hnonneg : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ X t)
    (hquad : ∀ t ∈ Icc (0 : ℝ) T, X t ≤ b * (X t) ^ 2) :
    ∀ t ∈ Icc (0 : ℝ) T, X t = 0 := by
  let R : ℝ := 1 / (2 * b)
  have hR : 0 < R := by dsimp [R]; positivity
  have hRcalc : b * R ^ 2 = R / 2 := by
    dsimp [R]
    field_simp [ne_of_gt hb]
    <;> ring
  have hbarrier : 0 + b * R ^ 2 < R := by
    rw [zero_add, hRcalc]
    linarith
  have hbound := CONTINUOUS_QUADRATIC_BARRIER X 0 b R T hcont
    (by rw [hzero]; exact hR) hbarrier
    (by intro t ht; simpa only [zero_add] using hquad t ht)
  intro t ht
  apply le_antisymm _ (hnonneg t ht)
  by_contra hnot
  have hpos : 0 < X t := lt_of_not_ge hnot
  have hmul := mul_lt_mul_of_pos_left (hbound t ht) hb
  have hbR : b * R = 1 / 2 := by
    dsimp [R]
    field_simp [ne_of_gt hb]
    <;> ring
  rw [hbR] at hmul
  have hprod := mul_pos (show 0 < 1 - b * X t by linarith) hpos
  have hq := hquad t ht
  nlinarith

/-- The uniform 2h barrier, including the zero datum case. -/
theorem QUADRATIC_BARRIER_LE_TWO_HEAT_BUDGET
    (X : ℝ → ℝ) (h b T : ℝ) (hh : 0 ≤ h) (hb : 0 < b)
    (hsmall : 4 * b * h < 1)
    (hcont : ContinuousOn X (Icc 0 T))
    (hzero : X 0 = 0)
    (hnonneg : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ X t)
    (hquad : ∀ t ∈ Icc (0 : ℝ) T, X t ≤ h + b * (X t) ^ 2) :
    ∀ t ∈ Icc (0 : ℝ) T, X t ≤ 2 * h := by
  rcases eq_or_lt_of_le hh with hzeroHeat | hposHeat
  · subst h
    intro t ht
    have hX := QUADRATIC_BARRIER_ZERO_HEAT_BUDGET X b T hb hcont hzero
      hnonneg (by intro r hr; simpa only [zero_add] using hquad r hr) t ht
    simp only [hX, mul_zero, le_refl]
  · intro t ht
    exact (QUADRATIC_BARRIER_LT_TWO_HEAT_BUDGET X h b T hposHeat
      hsmall hcont hzero hquad t ht).le

/-- Squaring the barrier gives the exact caloric integral budget factor 4. -/
theorem QUADRATIC_BARRIER_SQUARE_BUDGET
    (X : ℝ → ℝ) (h b T : ℝ) (hh : 0 ≤ h) (hb : 0 < b)
    (hsmall : 4 * b * h < 1)
    (hcont : ContinuousOn X (Icc 0 T))
    (hzero : X 0 = 0)
    (hnonneg : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ X t)
    (hquad : ∀ t ∈ Icc (0 : ℝ) T, X t ≤ h + b * (X t) ^ 2) :
    ∀ t ∈ Icc (0 : ℝ) T, (X t) ^ 2 ≤ 4 * h ^ 2 := by
  intro t ht
  have hbound := QUADRATIC_BARRIER_LE_TWO_HEAT_BUDGET
    X h b T hh hb hsmall hcont hzero hnonneg hquad t ht
  nlinarith [hnonneg t ht]

end
end QuasiFeffermanB

