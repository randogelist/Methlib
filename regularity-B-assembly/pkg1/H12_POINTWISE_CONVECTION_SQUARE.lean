import H12_FOURIER_FOUNDATIONS
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

set_option autoImplicit false

open scoped BigOperators

noncomputable section

namespace H12PointwiseConvectionSquare

abbrev Vec3 := Fin 3 → ℝ
abbrev Grad3 := Fin 3 → Fin 3 → ℝ

def dot3 (a b : Vec3) : ℝ :=
  ∑ i : Fin 3, a i * b i

def sqNorm3 (a : Vec3) : ℝ :=
  ∑ i : Fin 3, a i ^ 2

def columnSq (G : Grad3) (i : Fin 3) : ℝ :=
  sqNorm3 (fun j => G j i)

def frobeniusSq (G : Grad3) : ℝ :=
  ∑ i : Fin 3, columnSq G i

def convection (u : Vec3) (G : Grad3) : Vec3 :=
  fun i => dot3 u (fun j => G j i)

def pairing (u : Vec3) (G : Grad3) (w : Vec3) : ℝ :=
  dot3 (convection u G) w

theorem sqNorm3_nonneg (a : Vec3) :
    0 ≤ sqNorm3 a := by
  unfold sqNorm3
  exact Finset.sum_nonneg (fun i hi => sq_nonneg (a i))

theorem columnSq_nonneg (G : Grad3) (i : Fin 3) :
    0 ≤ columnSq G i :=
  sqNorm3_nonneg (fun j => G j i)

theorem frobeniusSq_nonneg (G : Grad3) :
    0 ≤ frobeniusSq G := by
  unfold frobeniusSq
  exact Finset.sum_nonneg (fun i hi => columnSq_nonneg G i)

theorem dot3_sq_le (a b : Vec3) :
    (dot3 a b) ^ 2 ≤ sqNorm3 a * sqNorm3 b := by
  unfold dot3 sqNorm3
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    (s := Finset.univ)
    (r := fun i => a i * b i)
    (f := fun i => a i ^ 2)
    (g := fun i => b i ^ 2)
  · intro i hi
    exact sq_nonneg (a i)
  · intro i hi
    exact sq_nonneg (b i)
  · intro i hi
    exact le_of_eq (by ring)

theorem convection_component_sq_le
    (u : Vec3) (G : Grad3) (i : Fin 3) :
    (convection u G i) ^ 2 ≤
      sqNorm3 u * columnSq G i := by
  exact dot3_sq_le u (fun j => G j i)

theorem convection_sqNorm_le
    (u : Vec3) (G : Grad3) :
    sqNorm3 (convection u G) ≤
      sqNorm3 u * frobeniusSq G := by
  calc
    sqNorm3 (convection u G)
        = ∑ i : Fin 3, (convection u G i) ^ 2 := rfl
    _ ≤ ∑ i : Fin 3, sqNorm3 u * columnSq G i := by
          exact Finset.sum_le_sum
            (fun i hi => convection_component_sq_le u G i)
    _ = sqNorm3 u * frobeniusSq G := by
          rw [← Finset.mul_sum]
          rfl

theorem pairing_sq_le
    (u : Vec3) (G : Grad3) (w : Vec3) :
    (pairing u G w) ^ 2 ≤
      sqNorm3 u * frobeniusSq G * sqNorm3 w := by
  have hdot :
      (pairing u G w) ^ 2 ≤
        sqNorm3 (convection u G) * sqNorm3 w := by
    exact dot3_sq_le (convection u G) w
  have hconv :
      sqNorm3 (convection u G) ≤
        sqNorm3 u * frobeniusSq G :=
    convection_sqNorm_le u G
  have hw : 0 ≤ sqNorm3 w :=
    sqNorm3_nonneg w
  exact hdot.trans
    (mul_le_mul_of_nonneg_right hconv hw)

structure PointwiseConvectionSquareBundle : Prop where
  cauchy :
    ∀ a b : Vec3,
      (dot3 a b) ^ 2 ≤ sqNorm3 a * sqNorm3 b
  convection :
    ∀ (u : Vec3) (G : Grad3),
      sqNorm3 (H12PointwiseConvectionSquare.convection u G) ≤
        sqNorm3 u * frobeniusSq G
  pairing :
    ∀ (u : Vec3) (G : Grad3) (w : Vec3),
      (H12PointwiseConvectionSquare.pairing u G w) ^ 2 ≤
        sqNorm3 u * frobeniusSq G * sqNorm3 w

theorem H12_POINTWISE_CONVECTION_SQUARE :
    PointwiseConvectionSquareBundle :=
  ⟨dot3_sq_le, convection_sqNorm_le, pairing_sq_le⟩

end H12PointwiseConvectionSquare
