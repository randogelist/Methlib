import Mathlib.Data.Real.Basic

set_option autoImplicit false

namespace CEATheta

structure BKQRHalfMomentCore (a : ℝ) (m : ℝ → ℝ) : Prop where
  ha : 1 ≤ a
  nonneg : ∀ x, 0 ≤ x → 0 ≤ m x
  scaleDown :
    ∀ x, 0 ≤ x →
      m (x / a) ≤ m x
  scaleUp :
    ∀ x, 0 ≤ x →
      m x ≤ m (a * x)
  cocycleDown :
    ∀ x, 0 ≤ x →
      m (x / a) * m x = 1 + a * x
  cocycleUp :
    ∀ x, 0 ≤ x →
      m x * m (a * x) = 1 + a ^ 2 * x

theorem bkqr_halfMoment_sq_lower
    {a : ℝ} {m : ℝ → ℝ}
    (c : BKQRHalfMomentCore a m)
    {x : ℝ} (hx : 0 ≤ x) :
    1 + a * x ≤ (m x) ^ 2 := by
  have hm : 0 ≤ m x := c.nonneg x hx
  have hprod :
      m (x / a) * m x ≤ m x * m x :=
    mul_le_mul_of_nonneg_right (c.scaleDown x hx) hm
  calc
    1 + a * x
        = m (x / a) * m x := (c.cocycleDown x hx).symm
    _ ≤ m x * m x := hprod
    _ = (m x) ^ 2 := by
      simp [pow_two]

theorem bkqr_halfMoment_sq_upper
    {a : ℝ} {m : ℝ → ℝ}
    (c : BKQRHalfMomentCore a m)
    {x : ℝ} (hx : 0 ≤ x) :
    (m x) ^ 2 ≤ 1 + a ^ 2 * x := by
  have hm : 0 ≤ m x := c.nonneg x hx
  have hprod :
      m x * m x ≤ m x * m (a * x) :=
    mul_le_mul_of_nonneg_left (c.scaleUp x hx) hm
  calc
    (m x) ^ 2
        = m x * m x := by
          simp [pow_two]
    _ ≤ m x * m (a * x) := hprod
    _ = 1 + a ^ 2 * x := c.cocycleUp x hx

theorem bkqr_halfMoment_sq_controls_one_add
    {a : ℝ} {m : ℝ → ℝ}
    (c : BKQRHalfMomentCore a m)
    {x : ℝ} (hx : 0 ≤ x) :
    1 + x ≤ (m x) ^ 2 := by
  have hxa : x ≤ a * x := by
    have h := mul_le_mul_of_nonneg_right c.ha hx
    simpa using h
  have hone : 1 + x ≤ 1 + a * x := by
    simpa [add_comm] using (add_le_add_left hxa 1)
  exact hone.trans (bkqr_halfMoment_sq_lower c hx)

theorem bkqr_halfMoment_squared_comparison
    {a : ℝ} {m : ℝ → ℝ}
    (c : BKQRHalfMomentCore a m)
    {x : ℝ} (hx : 0 ≤ x) :
    (1 + a * x ≤ (m x) ^ 2) ∧
    ((m x) ^ 2 ≤ 1 + a ^ 2 * x) := by
  exact ⟨bkqr_halfMoment_sq_lower c hx,
    bkqr_halfMoment_sq_upper c hx⟩

#print axioms CEATheta.bkqr_halfMoment_sq_lower
#print axioms CEATheta.bkqr_halfMoment_sq_upper
#print axioms CEATheta.bkqr_halfMoment_sq_controls_one_add
#print axioms CEATheta.bkqr_halfMoment_squared_comparison

end CEATheta
