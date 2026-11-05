import Mathlib

namespace CondFeffA

open Polynomial
open scoped BigOperators Polynomial

/-- An upper bound for the absolute linear coefficient, submultiplicative
because only the constant and linear coefficients contribute at order one. -/
noncomputable def firstTwoCoeffNorm (p : ℝ[X]) : ℝ :=
  |p.coeff 0| + |p.coeff 1|

private theorem firstTwoCoeffNorm_nonneg (p : ℝ[X]) : 0 ≤ firstTwoCoeffNorm p :=
  add_nonneg (abs_nonneg _) (abs_nonneg _)

private theorem firstTwoCoeffNorm_mul_le (p q : ℝ[X]) :
    firstTwoCoeffNorm (p * q) ≤ firstTwoCoeffNorm p * firstTwoCoeffNorm q := by
  unfold firstTwoCoeffNorm
  rw [Polynomial.mul_coeff_zero, Polynomial.mul_coeff_one, abs_mul]
  have hh := abs_add_le (p.coeff 0 * q.coeff 1) (p.coeff 1 * q.coeff 0)
  simp only [abs_mul] at hh
  nlinarith [mul_nonneg (abs_nonneg (p.coeff 1)) (abs_nonneg (q.coeff 1))]

private theorem firstTwoCoeffNorm_prod_le {ι : Type*} (s : Finset ι) (f : ι → ℝ[X]) :
    firstTwoCoeffNorm (∏ i ∈ s, f i) ≤ ∏ i ∈ s, firstTwoCoeffNorm (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [firstTwoCoeffNorm, Polynomial.coeff_one]
  | insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    exact (firstTwoCoeffNorm_mul_le _ _).trans
      (mul_le_mul_of_nonneg_left ih (firstTwoCoeffNorm_nonneg _))

private theorem firstTwoCoeffNorm_basisDivisor (x y : ℝ) :
    firstTwoCoeffNorm (Lagrange.basisDivisor x y) = (|y| + 1) / |x - y| := by
  have hzero : ((X - C y : ℝ[X]).coeff 0) = -y := by simp
  have hone : ((X - C y : ℝ[X]).coeff 1) = 1 := by simp
  simp only [firstTwoCoeffNorm, Lagrange.basisDivisor, Polynomial.coeff_C_mul,
    hzero, hone, abs_mul, abs_neg, abs_inv, mul_one, div_eq_mul_inv]
  ring

/-- A coefficient estimate for the actual Lagrange basis. There is no loss
depending on the amplitude jet: all nontrivial geometry occurs in the
product of distances from x to the other nodes. -/
theorem lagrange_linear_coeff_le_distances (s : Finset ℝ) (x R : ℝ)
    (hR : ∀ y ∈ s, |y| ≤ R) :
    |(Lagrange.basis s id x).coeff 1| ≤
      (R + 1) ^ (s.erase x).card / ∏ y ∈ s.erase x, |x - y| := by
  classical
  calc
    |(Lagrange.basis s id x).coeff 1| ≤ firstTwoCoeffNorm (Lagrange.basis s id x) :=
      le_add_of_nonneg_left (abs_nonneg _)
    _ ≤ ∏ y ∈ s.erase x, firstTwoCoeffNorm (Lagrange.basisDivisor x y) := by
      simpa only [Lagrange.basis, id_eq] using
        firstTwoCoeffNorm_prod_le (s.erase x) (Lagrange.basisDivisor x)
    _ = ∏ y ∈ s.erase x, (|y| + 1) / |x - y| := by
      simp only [firstTwoCoeffNorm_basisDivisor]
    _ ≤ ∏ y ∈ s.erase x, (R + 1) / |x - y| := by
      apply Finset.prod_le_prod
      · intro y hy
        positivity
      · intro y hy
        exact div_le_div_of_nonneg_right
          (add_le_add (hR y (Finset.mem_of_mem_erase hy)) (le_refl (1 : ℝ))) (abs_nonneg _)
    _ = (R + 1) ^ (s.erase x).card / ∏ y ∈ s.erase x, |x - y| := by
      simp only [Finset.prod_div_distrib, Finset.prod_const]

/-- The total weight estimate reduces to the reciprocal products of pairwise
distances in the node set. The polynomial contribution costs (R+1)^d. -/
theorem lagrange_linear_coeff_sum_of_reciprocal_distances
    (s : Finset ℝ) (d : ℕ) (R B : ℝ) (hcard : s.card = d + 1)
    (hR0 : 0 ≤ R) (hR : ∀ y ∈ s, |y| ≤ R)
    (hgaps : (∑ x ∈ s, 1 / ∏ y ∈ s.erase x, |x - y|) ≤ B ^ d) :
    (∑ x ∈ s, |(Lagrange.basis s id x).coeff 1|) ≤ ((R + 1) * B) ^ d := by
  classical
  calc
    (∑ x ∈ s, |(Lagrange.basis s id x).coeff 1|)
      ≤ ∑ x ∈ s, (R + 1) ^ d * (1 / ∏ y ∈ s.erase x, |x - y|) := by
        apply Finset.sum_le_sum
        intro x hx
        have he : (s.erase x).card = d :=
          (Finset.card_erase_of_mem hx).trans (by omega)
        simpa only [he, div_eq_mul_inv, one_mul] using
          lagrange_linear_coeff_le_distances s x R hR
    _ = (R + 1) ^ d * ∑ x ∈ s, 1 / ∏ y ∈ s.erase x, |x - y| :=
      (Finset.mul_sum ..).symm
    _ ≤ (R + 1) ^ d * B ^ d :=
      mul_le_mul_of_nonneg_left hgaps (pow_nonneg (by linarith) _)
    _ = ((R + 1) * B) ^ d := (mul_pow _ _ _).symm


/-- Reindex the scalar gap budget along an injective list of real nodes. -/
theorem reciprocal_distances_map {ι : Type*} [DecidableEq ι]
    (t : Finset ι) (e : ι ↪ ℝ) :
    (∑ x ∈ t.map e, 1 / ∏ y ∈ (t.map e).erase x, |x - y|) =
      ∑ i ∈ t, 1 / ∏ j ∈ t.erase i, |e i - e j| := by
  classical
  rw [Finset.sum_map]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.map_erase e t i, Finset.prod_map]

end CondFeffA
