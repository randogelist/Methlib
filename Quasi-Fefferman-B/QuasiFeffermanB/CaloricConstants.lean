import QuasiFeffermanB.CaloricBarrier

/-! Exact numerical constants for the strict caloric quadratic barrier. -/

set_option autoImplicit false
set_option Elab.async true

open Set

namespace QuasiFeffermanB
noncomputable section

/-- The exact symmetric Duhamel coefficient. -/
def caloricBilinearConstant (ν : ℝ) : ℝ :=
  1 / (2 * Real.sqrt (2 * ν))

/-- Heat-orbit budget corresponding to the caloric quadratic form Q. -/
def caloricHeatBudget (ν Q : ℝ) : ℝ :=
  Q / Real.sqrt ν

theorem caloricBilinearConstant_pos (ν : ℝ) (hν : 0 < ν) :
    0 < caloricBilinearConstant ν := by
  unfold caloricBilinearConstant
  positivity

theorem caloricBilinearConstant_sq (ν : ℝ) (hν : 0 < ν) :
    caloricBilinearConstant ν ^ 2 = 1 / (8 * ν) := by
  unfold caloricBilinearConstant
  rw [div_pow, mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 2 * ν)]
  congr 1 <;> ring

theorem caloricHeatBudget_nonneg (ν Q : ℝ) (hQ : 0 ≤ Q) :
    0 ≤ caloricHeatBudget ν Q :=
  div_nonneg hQ (Real.sqrt_nonneg ν)

theorem caloricHeatBudget_sq (ν Q : ℝ) (hν : 0 < ν) :
    caloricHeatBudget ν Q ^ 2 = Q ^ 2 / ν := by
  unfold caloricHeatBudget
  rw [div_pow, Real.sq_sqrt hν.le]

/-- The strict squared caloric criterion gives exactly the discriminant needed
by the continuous quadratic barrier. -/
theorem STRICT_CALORIC_DISCRIMINANT
    (ν Q : ℝ) (hν : 0 < ν) (hQ : 0 ≤ Q)
    (hsmall : Q ^ 2 < ν ^ 2 / 2) :
    4 * caloricBilinearConstant ν * caloricHeatBudget ν Q < 1 := by
  have hcalc :
      (4 * caloricBilinearConstant ν * caloricHeatBudget ν Q) ^ 2 =
        2 * Q ^ 2 / ν ^ 2 := by
    simp only [mul_pow, caloricBilinearConstant_sq ν hν,
      caloricHeatBudget_sq ν Q hν]
    field_simp [ne_of_gt hν]
    <;> ring
  have hsq : (4 * caloricBilinearConstant ν * caloricHeatBudget ν Q) ^ 2 < 1 := by
    rw [hcalc]
    apply (div_lt_one (sq_pos_of_pos hν)).mpr
    linarith
  have hn : 0 ≤ 4 * caloricBilinearConstant ν * caloricHeatBudget ν Q :=
    mul_nonneg (mul_nonneg (by norm_num) (caloricBilinearConstant_pos ν hν).le)
      (caloricHeatBudget_nonneg ν Q hQ)
  nlinarith

/-- Numerical specialization of the barrier to the exact caloric constants.
The scalar quadratic estimate is the explicitly displayed analytic input. -/
theorem STRICT_CALORIC_QUADRATIC_BUDGET
    (X : ℝ → ℝ) (ν Q T : ℝ) (hν : 0 < ν) (hQ : 0 ≤ Q)
    (hsmall : Q ^ 2 < ν ^ 2 / 2)
    (hcont : ContinuousOn X (Icc 0 T))
    (hzero : X 0 = 0)
    (hnonneg : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ X t)
    (hquad : ∀ t ∈ Icc (0 : ℝ) T,
      X t ≤ caloricHeatBudget ν Q + caloricBilinearConstant ν * (X t) ^ 2) :
    ∀ t ∈ Icc (0 : ℝ) T, (X t) ^ 2 ≤ 4 * Q ^ 2 / ν := by
  intro t ht
  have hb := QUADRATIC_BARRIER_SQUARE_BUDGET X
    (caloricHeatBudget ν Q) (caloricBilinearConstant ν) T
    (caloricHeatBudget_nonneg ν Q hQ) (caloricBilinearConstant_pos ν hν)
    (STRICT_CALORIC_DISCRIMINANT ν Q hν hQ hsmall)
    hcont hzero hnonneg hquad t ht
  rw [caloricHeatBudget_sq ν Q hν] at hb
  simpa only [mul_div_assoc] using hb


end
end QuasiFeffermanB
