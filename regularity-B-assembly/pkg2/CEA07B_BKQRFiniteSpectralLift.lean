import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

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
    (m x) ^ 2
        = m x * m x := by simp [pow_two]
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

theorem bkqr_halfMoment_finiteSpectral_lower
    {ι : Type*}
    {a : ℝ} {m : ℝ → ℝ}
    (c : BKQRHalfMomentCore a m)
    (s : Finset ι)
    (energy x : ι → ℝ)
    (henergy : ∀ i, 0 ≤ energy i)
    (hx : ∀ i, 0 ≤ x i) :
    Finset.sum s (fun i => Real.sqrt (1 + a * x i) * energy i)
      ≤
    Finset.sum s (fun i => m (x i) * energy i) := by
  apply Finset.sum_le_sum
  intro i hi
  exact mul_le_mul_of_nonneg_right
    (bkqr_halfMoment_sqrt_lower c (hx i))
    (henergy i)

theorem bkqr_halfMoment_finiteSpectral_upper
    {ι : Type*}
    {a : ℝ} {m : ℝ → ℝ}
    (c : BKQRHalfMomentCore a m)
    (s : Finset ι)
    (energy x : ι → ℝ)
    (henergy : ∀ i, 0 ≤ energy i)
    (hx : ∀ i, 0 ≤ x i) :
    Finset.sum s (fun i => m (x i) * energy i)
      ≤
    Finset.sum s (fun i => Real.sqrt (1 + a ^ 2 * x i) * energy i) := by
  apply Finset.sum_le_sum
  intro i hi
  exact mul_le_mul_of_nonneg_right
    (bkqr_halfMoment_sqrt_upper c (hx i))
    (henergy i)

theorem bkqr_halfMoment_finiteSpectral_comparison
    {ι : Type*}
    {a : ℝ} {m : ℝ → ℝ}
    (c : BKQRHalfMomentCore a m)
    (s : Finset ι)
    (energy x : ι → ℝ)
    (henergy : ∀ i, 0 ≤ energy i)
    (hx : ∀ i, 0 ≤ x i) :
    (Finset.sum s (fun i => Real.sqrt (1 + a * x i) * energy i)
      ≤
     Finset.sum s (fun i => m (x i) * energy i))
    ∧
    (Finset.sum s (fun i => m (x i) * energy i)
      ≤
     Finset.sum s (fun i => Real.sqrt (1 + a ^ 2 * x i) * energy i)) := by
  exact ⟨
    bkqr_halfMoment_finiteSpectral_lower c s energy x henergy hx,
    bkqr_halfMoment_finiteSpectral_upper c s energy x henergy hx
  ⟩

#print axioms CEATheta.bkqr_halfMoment_sqrt_lower
#print axioms CEATheta.bkqr_halfMoment_sqrt_upper
#print axioms CEATheta.bkqr_halfMoment_finiteSpectral_lower
#print axioms CEATheta.bkqr_halfMoment_finiteSpectral_upper
#print axioms CEATheta.bkqr_halfMoment_finiteSpectral_comparison

end CEATheta
