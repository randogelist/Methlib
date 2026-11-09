import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.Ring

set_option autoImplicit false

noncomputable section

namespace CEATheta

def bkqrHalfFactor (q a x : ℝ) (n : ℕ) : ℝ :=
  (1 + a * q ^ n * x) / (1 + q ^ n * x)

noncomputable def bkqrHalfMoment (q a x : ℝ) : ℝ :=
  ∏' n : ℕ, bkqrHalfFactor q a x n

def bkqrHalfDeviation (q a x : ℝ) (n : ℕ) : ℝ :=
  ((a - 1) * x * q ^ n) / (1 + q ^ n * x)

theorem bkqrHalfFactor_den_pos
    {q x : ℝ} (hq : 0 ≤ q) (hx : 0 ≤ x) (n : ℕ) :
    0 < 1 + q ^ n * x := by
  have hp : 0 ≤ q ^ n := pow_nonneg hq n
  have hpx : 0 ≤ q ^ n * x := mul_nonneg hp hx
  exact add_pos_of_pos_of_nonneg zero_lt_one hpx

theorem bkqrHalfFactor_eq_one_add_deviation
    {q a x : ℝ} (hq : 0 ≤ q) (hx : 0 ≤ x) (n : ℕ) :
    bkqrHalfFactor q a x n = 1 + bkqrHalfDeviation q a x n := by
  unfold bkqrHalfFactor bkqrHalfDeviation
  have hden := bkqrHalfFactor_den_pos hq hx n
  field_simp [hden.ne']
  ring

theorem bkqrHalfDeviation_nonneg
    {q a x : ℝ}
    (hq : 0 ≤ q) (ha : 1 ≤ a) (hx : 0 ≤ x) (n : ℕ) :
    0 ≤ bkqrHalfDeviation q a x n := by
  unfold bkqrHalfDeviation
  have hnum :
      0 ≤ (a - 1) * x * q ^ n :=
    mul_nonneg
      (mul_nonneg (sub_nonneg.mpr ha) hx)
      (pow_nonneg hq n)
  exact div_nonneg hnum (bkqrHalfFactor_den_pos hq hx n).le

theorem bkqrHalfDeviation_le_geometric
    {q a x : ℝ}
    (hq : 0 ≤ q) (ha : 1 ≤ a) (hx : 0 ≤ x) (n : ℕ) :
    bkqrHalfDeviation q a x n ≤ ((a - 1) * x) * q ^ n := by
  unfold bkqrHalfDeviation
  let C : ℝ := (a - 1) * x
  have hC : 0 ≤ C := mul_nonneg (sub_nonneg.mpr ha) hx
  have hqn : 0 ≤ q ^ n := pow_nonneg hq n
  have hnum : 0 ≤ C * q ^ n := mul_nonneg hC hqn
  have hden := bkqrHalfFactor_den_pos hq hx n
  apply (div_le_iff₀ hden).2
  have ht : 0 ≤ q ^ n * x := mul_nonneg hqn hx
  have hmul :
      C * q ^ n ≤ (C * q ^ n) * (1 + q ^ n * x) := by
    calc
      C * q ^ n = (C * q ^ n) * 1 := by ring
      _ ≤ (C * q ^ n) * (1 + q ^ n * x) :=
        mul_le_mul_of_nonneg_left
          (le_add_of_nonneg_right ht) hnum
  simpa [C, mul_assoc] using hmul

theorem summable_bkqrHalfDeviation
    {q a x : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (ha : 1 ≤ a) (hx : 0 ≤ x) :
    Summable (bkqrHalfDeviation q a x) := by
  have hgeom :
      Summable (fun n : ℕ => ((a - 1) * x) * q ^ n) :=
    (summable_geometric_of_lt_one hq0 hq1).mul_left ((a - 1) * x)
  exact Summable.of_nonneg_of_le
    (fun n => bkqrHalfDeviation_nonneg hq0 ha hx n)
    (fun n => bkqrHalfDeviation_le_geometric hq0 ha hx n)
    hgeom

theorem multipliable_bkqrHalfFactor
    {q a x : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (ha : 1 ≤ a) (hx : 0 ≤ x) :
    Multipliable (bkqrHalfFactor q a x) := by
  have hdev := summable_bkqrHalfDeviation hq0 hq1 ha hx
  have hm :
      Multipliable
        (fun n : ℕ => 1 + bkqrHalfDeviation q a x n) :=
    Real.multipliable_one_add_of_summable hdev
  exact hm.congr
    (fun n => (bkqrHalfFactor_eq_one_add_deviation hq0 hx n).symm)

theorem one_le_bkqrHalfFactor
    {q a x : ℝ}
    (hq : 0 ≤ q) (ha : 1 ≤ a) (hx : 0 ≤ x) (n : ℕ) :
    1 ≤ bkqrHalfFactor q a x n := by
  unfold bkqrHalfFactor
  have hden := bkqrHalfFactor_den_pos hq hx n
  apply (le_div_iff₀ hden).2
  have hqn : 0 ≤ q ^ n := pow_nonneg hq n
  have ht : 0 ≤ q ^ n * x := mul_nonneg hqn hx
  have hmul : q ^ n * x ≤ a * (q ^ n * x) := by
    simpa using (mul_le_mul_of_nonneg_right ha ht)
  have hadd :
      1 + q ^ n * x ≤ 1 + a * (q ^ n * x) := by
    simpa [add_comm] using (add_le_add_left hmul 1)
  simpa [mul_assoc] using hadd

theorem bkqrHalfMoment_one_le
    {q a x : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (ha : 1 ≤ a) (hx : 0 ≤ x) :
    1 ≤ bkqrHalfMoment q a x := by
  have hm := multipliable_bkqrHalfFactor hq0 hq1 ha hx
  unfold bkqrHalfMoment
  apply le_of_tendsto' hm.hasProd.tendsto_prod_nat
  intro n
  exact Finset.one_le_prod₀
    (fun i hi => one_le_bkqrHalfFactor hq0 ha hx i)

theorem bkqrHalfFactor_mono
    {q a x y : ℝ}
    (hq : 0 ≤ q) (ha : 1 ≤ a)
    (hx : 0 ≤ x) (hxy : x ≤ y)
    (n : ℕ) :
    bkqrHalfFactor q a x n ≤ bkqrHalfFactor q a y n := by
  have hy : 0 ≤ y := hx.trans hxy
  unfold bkqrHalfFactor
  have hdx := bkqrHalfFactor_den_pos hq hx n
  have hdy := bkqrHalfFactor_den_pos hq hy n
  apply (div_le_div_iff₀ hdx hdy).2
  have hqn : 0 ≤ q ^ n := pow_nonneg hq n
  have hcore :
      0 ≤ (a - 1) * q ^ n * (y - x) :=
    mul_nonneg
      (mul_nonneg (sub_nonneg.mpr ha) hqn)
      (sub_nonneg.mpr hxy)
  have hid :
      (1 + a * q ^ n * y) * (1 + q ^ n * x)
        -
      (1 + a * q ^ n * x) * (1 + q ^ n * y)
        =
      (a - 1) * q ^ n * (y - x) := by
    ring
  have hdiff :
      0 ≤
        (1 + a * q ^ n * y) * (1 + q ^ n * x)
          -
        (1 + a * q ^ n * x) * (1 + q ^ n * y) := by
    rw [hid]
    exact hcore
  exact sub_nonneg.mp hdiff

theorem bkqrHalfMoment_mono
    {q a x y : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (ha : 1 ≤ a)
    (hx : 0 ≤ x) (hxy : x ≤ y) :
    bkqrHalfMoment q a x ≤ bkqrHalfMoment q a y := by
  have hy : 0 ≤ y := hx.trans hxy
  have hmx := multipliable_bkqrHalfFactor hq0 hq1 ha hx
  have hmy := multipliable_bkqrHalfFactor hq0 hq1 ha hy
  unfold bkqrHalfMoment
  apply le_of_tendsto_of_tendsto'
    hmx.hasProd.tendsto_prod_nat
    hmy.hasProd.tendsto_prod_nat
  intro n
  apply Finset.prod_le_prod₀
  · intro i hi
    exact zero_le_one.trans (one_le_bkqrHalfFactor hq0 ha hx i)
  · intro i hi
    exact bkqrHalfFactor_mono hq0 ha hx hxy i

theorem bkqrHalfMoment_nonneg
    {q a x : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (ha : 1 ≤ a) (hx : 0 ≤ x) :
    0 ≤ bkqrHalfMoment q a x :=
  zero_le_one.trans (bkqrHalfMoment_one_le hq0 hq1 ha hx)

#print axioms CEATheta.bkqrHalfFactor_eq_one_add_deviation
#print axioms CEATheta.summable_bkqrHalfDeviation
#print axioms CEATheta.multipliable_bkqrHalfFactor
#print axioms CEATheta.bkqrHalfMoment_one_le
#print axioms CEATheta.bkqrHalfFactor_mono
#print axioms CEATheta.bkqrHalfMoment_mono
#print axioms CEATheta.bkqrHalfMoment_nonneg

end CEATheta
