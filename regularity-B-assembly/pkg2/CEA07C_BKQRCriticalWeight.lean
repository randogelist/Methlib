import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring

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
    1 + a * x = m (x / a) * m x := (c.cocycleDown x hx).symm
    _ ≤ m x * m x := hprod
    _ = (m x) ^ 2 := by simp [pow_two]

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
    (m x) ^ 2 = m x * m x := by simp [pow_two]
    _ ≤ m x * m (a * x) := hprod
    _ = 1 + a ^ 2 * x := c.cocycleUp x hx

theorem bkqr_halfMoment_sqrt_lower
    {a : ℝ} {m : ℝ → ℝ}
    (c : BKQRHalfMomentCore a m)
    {x : ℝ} (hx : 0 ≤ x) :
    Real.sqrt (1 + a * x) ≤ m x := by
  exact (Real.sqrt_le_iff).2
    ⟨c.nonneg x hx, bkqr_halfMoment_sq_lower c hx⟩

theorem bkqr_halfMoment_sqrt_upper
    {a : ℝ} {m : ℝ → ℝ}
    (c : BKQRHalfMomentCore a m)
    {x : ℝ} (hx : 0 ≤ x) :
    m x ≤ Real.sqrt (1 + a ^ 2 * x) := by
  exact Real.le_sqrt_of_sq_le (bkqr_halfMoment_sq_upper c hx)

noncomputable def criticalWeight (x : ℝ) : ℝ :=
  1 + Real.sqrt x

theorem bkqr_criticalWeight_le_two_mul_halfMoment
    {a : ℝ} {m : ℝ → ℝ}
    (c : BKQRHalfMomentCore a m)
    {x : ℝ} (hx : 0 ≤ x) :
    criticalWeight x ≤ 2 * m x := by
  have ha0 : 0 ≤ a := zero_le_one.trans c.ha
  have hxa : x ≤ a * x := by
    have h := mul_le_mul_of_nonneg_right c.ha hx
    simpa using h
  have hsx :
      Real.sqrt x ≤ Real.sqrt (1 + a * x) := by
    have h1 : x ≤ 1 + a * x := by
      exact hxa.trans (le_add_of_nonneg_left zero_le_one)
    exact Real.sqrt_le_sqrt h1
  have hax0 : 0 ≤ a * x := mul_nonneg ha0 hx
  have hone :
      1 ≤ Real.sqrt (1 + a * x) := by
    apply Real.le_sqrt_of_sq_le
    simpa using (le_add_of_nonneg_right hax0 : (1 : ℝ) ≤ 1 + a * x)
  have hcrit :
      criticalWeight x ≤ 2 * Real.sqrt (1 + a * x) := by
    dsimp [criticalWeight]
    have h := add_le_add hone hsx
    simpa [two_mul] using h
  exact hcrit.trans
    (mul_le_mul_of_nonneg_left
      (bkqr_halfMoment_sqrt_lower c hx)
      zero_le_two)

theorem bkqr_halfMoment_le_a_mul_criticalWeight
    {a : ℝ} {m : ℝ → ℝ}
    (c : BKQRHalfMomentCore a m)
    {x : ℝ} (hx : 0 ≤ x) :
    m x ≤ a * criticalWeight x := by
  have ha0 : 0 ≤ a := zero_le_one.trans c.ha
  have hs0 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have has0 : 0 ≤ a * Real.sqrt x := mul_nonneg ha0 hs0
  have hsqterm :
      (a * Real.sqrt x) ^ 2 = a ^ 2 * x := by
    rw [mul_pow, Real.sq_sqrt hx]
  have hcross :
      0 ≤ 2 * (a * Real.sqrt x) :=
    mul_nonneg zero_le_two has0
  have hsq :
      1 + a ^ 2 * x ≤ (1 + a * Real.sqrt x) ^ 2 := by
    calc
      1 + a ^ 2 * x
          ≤ 1 + a ^ 2 * x + 2 * (a * Real.sqrt x) :=
        le_add_of_nonneg_right hcross
      _ = 1 + (a * Real.sqrt x) ^ 2 + 2 * (a * Real.sqrt x) := by
        rw [hsqterm]
      _ = (1 + a * Real.sqrt x) ^ 2 := by
        ring
  have hsqrt :
      Real.sqrt (1 + a ^ 2 * x) ≤ 1 + a * Real.sqrt x := by
    exact (Real.sqrt_le_iff).2
      ⟨add_nonneg zero_le_one has0, hsq⟩
  have hscale :
      1 + a * Real.sqrt x ≤ a * criticalWeight x := by
    dsimp [criticalWeight]
    have h :
        1 + a * Real.sqrt x ≤ a + a * Real.sqrt x := by
      simpa [add_comm] using
        (add_le_add_right c.ha (a * Real.sqrt x))
    calc
      1 + a * Real.sqrt x
          ≤ a + a * Real.sqrt x := h
      _ = a * (1 + Real.sqrt x) := by
        ring
  exact (bkqr_halfMoment_sqrt_upper c hx).trans (hsqrt.trans hscale)

theorem bkqr_finite_criticalWeight_lower
    {ι : Type*}
    {a : ℝ} {m : ℝ → ℝ}
    (c : BKQRHalfMomentCore a m)
    (s : Finset ι)
    (energy x : ι → ℝ)
    (henergy : ∀ i, 0 ≤ energy i)
    (hx : ∀ i, 0 ≤ x i) :
    Finset.sum s (fun i => criticalWeight (x i) * energy i)
      ≤
    2 * Finset.sum s (fun i => m (x i) * energy i) := by
  have hsum :
      Finset.sum s (fun i => criticalWeight (x i) * energy i)
        ≤
      Finset.sum s (fun i => (2 * m (x i)) * energy i) := by
    apply Finset.sum_le_sum
    intro i hi
    exact mul_le_mul_of_nonneg_right
      (bkqr_criticalWeight_le_two_mul_halfMoment c (hx i))
      (henergy i)
  calc
    Finset.sum s (fun i => criticalWeight (x i) * energy i)
        ≤ Finset.sum s (fun i => (2 * m (x i)) * energy i) := hsum
    _ = Finset.sum s (fun i => 2 * (m (x i) * energy i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = 2 * Finset.sum s (fun i => m (x i) * energy i) := by
      rw [Finset.mul_sum]

theorem bkqr_finite_criticalWeight_upper
    {ι : Type*}
    {a : ℝ} {m : ℝ → ℝ}
    (c : BKQRHalfMomentCore a m)
    (s : Finset ι)
    (energy x : ι → ℝ)
    (henergy : ∀ i, 0 ≤ energy i)
    (hx : ∀ i, 0 ≤ x i) :
    Finset.sum s (fun i => m (x i) * energy i)
      ≤
    a * Finset.sum s (fun i => criticalWeight (x i) * energy i) := by
  have hsum :
      Finset.sum s (fun i => m (x i) * energy i)
        ≤
      Finset.sum s (fun i => (a * criticalWeight (x i)) * energy i) := by
    apply Finset.sum_le_sum
    intro i hi
    exact mul_le_mul_of_nonneg_right
      (bkqr_halfMoment_le_a_mul_criticalWeight c (hx i))
      (henergy i)
  calc
    Finset.sum s (fun i => m (x i) * energy i)
        ≤ Finset.sum s (fun i => (a * criticalWeight (x i)) * energy i) := hsum
    _ = Finset.sum s (fun i => a * (criticalWeight (x i) * energy i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = a * Finset.sum s (fun i => criticalWeight (x i) * energy i) := by
      rw [Finset.mul_sum]

theorem bkqr_finite_criticalWeight_comparison
    {ι : Type*}
    {a : ℝ} {m : ℝ → ℝ}
    (c : BKQRHalfMomentCore a m)
    (s : Finset ι)
    (energy x : ι → ℝ)
    (henergy : ∀ i, 0 ≤ energy i)
    (hx : ∀ i, 0 ≤ x i) :
    (Finset.sum s (fun i => criticalWeight (x i) * energy i)
      ≤ 2 * Finset.sum s (fun i => m (x i) * energy i))
    ∧
    (Finset.sum s (fun i => m (x i) * energy i)
      ≤ a * Finset.sum s (fun i => criticalWeight (x i) * energy i)) := by
  exact ⟨
    bkqr_finite_criticalWeight_lower c s energy x henergy hx,
    bkqr_finite_criticalWeight_upper c s energy x henergy hx
  ⟩

#print axioms CEATheta.bkqr_criticalWeight_le_two_mul_halfMoment
#print axioms CEATheta.bkqr_halfMoment_le_a_mul_criticalWeight
#print axioms CEATheta.bkqr_finite_criticalWeight_lower
#print axioms CEATheta.bkqr_finite_criticalWeight_upper
#print axioms CEATheta.bkqr_finite_criticalWeight_comparison

end CEATheta
