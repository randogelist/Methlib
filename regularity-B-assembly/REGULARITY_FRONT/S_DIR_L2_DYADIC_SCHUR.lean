import S_DIR_L2_PROOF_ASSEMBLY

set_option autoImplicit false
set_option maxHeartbeats 0

open scoped BigOperators

noncomputable section

namespace SDirL2

/-!
# S_DIR_L2: dyadic geometric / telescoping Schur frontier

This module is an additive proof layer, not a replacement for the frozen
physical root theorem. It reuses the native-audited plane projection and
finite Schur frontiers without changing their mathematical statements.

The following are proved without analytic admissions:
* Squared-radius bounds imply strict integer coordinate cube bounds.
* Every finite directional-plane subset of a dyadic radius ball has
  cardinal at most `16 * (2^j)^2`.
* A rational dyadic kernel obeys an exact telescoping domination.
* Every finite dyadic prefix has a uniform `4/r` sum bound.
* The resulting improved Serrin constant is no larger than the frozen one.

The global infinite-lattice partition and physical torus realization remain
separate endpoints. No `sorry` or assumed geometric area theorem is used.
-/

/-- Euclidean squared radius of an integer Fourier frequency. -/
def latticeRadiusSq (k : Mode3) : ℝ :=
  (k 0 : ℝ) ^ 2 + (k 1 : ℝ) ^ 2 + (k 2 : ℝ) ^ 2

/-- A strict Euclidean ball fits in a strict coordinate cube. -/
theorem S_DIR_L2_RADIUS_TO_STRICT_CUBE
    (R : ℕ) (hR : 0 < R) (k : Mode3)
    (hk : latticeRadiusSq k < (R : ℝ) ^ 2) (i : Fin 3) :
    -(R : ℤ) < k i ∧ k i < (R : ℤ) := by
  have hRreal : (0 : ℝ) < (R : ℝ) := by exact_mod_cast hR
  have h0 : (k 0 : ℝ) ^ 2 < (R : ℝ) ^ 2 := by
    dsimp [latticeRadiusSq] at hk
    nlinarith [sq_nonneg (k 1 : ℝ), sq_nonneg (k 2 : ℝ)]
  have h1 : (k 1 : ℝ) ^ 2 < (R : ℝ) ^ 2 := by
    dsimp [latticeRadiusSq] at hk
    nlinarith [sq_nonneg (k 0 : ℝ), sq_nonneg (k 2 : ℝ)]
  have h2 : (k 2 : ℝ) ^ 2 < (R : ℝ) ^ 2 := by
    dsimp [latticeRadiusSq] at hk
    nlinarith [sq_nonneg (k 0 : ℝ), sq_nonneg (k 1 : ℝ)]
  -- A squared inequality controls absolute value, but only after the
  -- nonlinear sign cases have been discharged explicitly.  The scalar
  -- helper also avoids relying on tactic normalization of Fin indices.
  have hscalar (x : ℝ) (hx : x ^ 2 < (R : ℝ) ^ 2) :
      -(R : ℝ) < x ∧ x < (R : ℝ) := by
    constructor
    · by_contra hn
      have hle : x ≤ -(R : ℝ) := le_of_not_gt hn
      have hleft : 0 ≤ -x - (R : ℝ) := by linarith
      have hright : 0 ≤ -x + (R : ℝ) := by linarith
      have hprod := mul_nonneg hleft hright
      nlinarith
    · by_contra hn
      have hle : (R : ℝ) ≤ x := le_of_not_gt hn
      have hleft : 0 ≤ x - (R : ℝ) := by linarith
      have hright : 0 ≤ x + (R : ℝ) := by linarith
      have hprod := mul_nonneg hleft hright
      nlinarith
  have hr : -(R : ℝ) < (k i : ℝ) ∧ (k i : ℝ) < (R : ℝ) := by
    fin_cases i
    · simpa using hscalar (k 0 : ℝ) h0
    · simpa using hscalar (k 1 : ℝ) h1
    · simpa using hscalar (k 2 : ℝ) h2
  constructor
  · exact_mod_cast hr.1
  · exact_mod_cast hr.2

/-- Strict coordinate bounds imply a uniform finite planar cube count. -/
theorem S_DIR_L2_PLANE_STRICT_CUBE_CARD
    (a : Mode3) (ha : a ≠ 0) (F : Finset Mode3)
    (R : ℕ) (hR : 0 < R)
    (hplane : ∀ k ∈ F, directionalDot a k = 0)
    (hcoords : ∀ k ∈ F, ∀ i : Fin 3,
       -(R : ℤ) < k i ∧ k i < (R : ℤ)) :
    F.card ≤ (2 * R - 1) ^ 2 := by
  have hcast : ((R - 1 : ℕ) : ℤ) = (R : ℤ) - 1 := by omega
  have hcube : ∀ k ∈ F, ∀ i : Fin 3,
      -((R - 1 : ℕ) : ℤ) ≤ k i ∧
      k i ≤ ((R - 1 : ℕ) : ℤ) := by
    intro k hk i
    have h := hcoords k hk i
    constructor <;> omega
  have hcount :=
    S_DIR_L2_PLANE_FINITE_CUBE_CARD a ha F (R - 1) hplane hcube
  have hside :
      (Finset.Icc (-((R - 1 : ℕ) : ℤ)) ((R - 1 : ℕ) : ℤ)).card
        = 2 * R - 1 := by
    rw [Int.card_Icc]
    omega
  simpa [hside] using hcount

/-- Dyadic radius-ball lattice count, uniform over nonzero integer axes. -/
theorem S_DIR_L2_DYADIC_PLANE_BALL_CARD
    (a : Mode3) (ha : a ≠ 0)
    (F : Finset Mode3) (j : ℕ)
    (hplane : ∀ k ∈ F, directionalDot a k = 0)
    (hupper : ∀ k ∈ F,
      latticeRadiusSq k < (((2 : ℕ) ^ (j + 1) : ℕ) : ℝ) ^ 2) :
    F.card ≤ 16 * ((2 : ℕ) ^ j) ^ 2 := by
  let R : ℕ := 2 ^ (j + 1)
  have hR : 0 < R := by dsimp [R]; positivity
  have hcoords : ∀ k ∈ F, ∀ i : Fin 3,
      -(R : ℤ) < k i ∧ k i < (R : ℤ) := by
    intro k hk i
    exact S_DIR_L2_RADIUS_TO_STRICT_CUBE R hR k (hupper k hk) i
  have hcount := S_DIR_L2_PLANE_STRICT_CUBE_CARD
    a ha F R hR hplane hcoords
  have hpow : R = 2 * (2 : ℕ) ^ j := by
    dsimp [R]
    rw [pow_succ]
    omega
  have hlin : 2 * R - 1 ≤ 4 * (2 : ℕ) ^ j := by
    rw [hpow]
    omega
  calc
    F.card ≤ (2 * R - 1) ^ 2 := hcount
    _ ≤ (4 * (2 : ℕ) ^ j) ^ 2 := by
      gcongr <;> exact hlin
    _ = 16 * ((2 : ℕ) ^ j) ^ 2 := by ring

/-- Rational dyadic heat-correlation summand. -/
def dyadicKernelTerm (r : ℝ) (j : ℕ) : ℝ :=
  (2 : ℝ) ^ j / (r ^ 2 + ((2 : ℝ) ^ j) ^ 2)

/-- Bounded increasing primitive for the dyadic correlation sum. -/
def dyadicPotential (r : ℝ) (j : ℕ) : ℝ :=
  (2 : ℝ) ^ j / (r + (2 : ℝ) ^ j)

/-- The key algebraic inequality; no integral or logarithm is required. -/
theorem S_DIR_L2_DYADIC_KERNEL_TELESCOPIC_STEP
    (r q : ℝ) (hr : 0 < r) (hq : 0 < q) :
    q / (r ^ 2 + q ^ 2) ≤
      (4 / r) * ((2 * q) / (r + 2 * q) - q / (r + q)) := by
  have hden :
      (r + 2 * q) * (r + q) ≤ 4 * (r ^ 2 + q ^ 2) := by
    nlinarith [sq_nonneg (r - q / 2), sq_nonneg q]
  have hbound :
      q / (r ^ 2 + q ^ 2) ≤
        (4 * q) / ((r + 2 * q) * (r + q)) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    calc
      q * ((r + 2 * q) * (r + q))
          ≤ q * (4 * (r ^ 2 + q ^ 2)) :=
            mul_le_mul_of_nonneg_left hden hq.le
      _ = (4 * q) * (r ^ 2 + q ^ 2) := by ring
  calc
    q / (r ^ 2 + q ^ 2)
        ≤ (4 * q) / ((r + 2 * q) * (r + q)) := hbound
    _ = (4 / r) * ((2 * q) / (r + 2 * q) - q / (r + q)) := by
      have hr0 : r ≠ 0 := ne_of_gt hr
      have hrq : r + q ≠ 0 := by positivity
      have hr2q : r + 2 * q ≠ 0 := by positivity
      field_simp [hr0, hrq, hr2q]
      <;> ring

/-- Exact dyadic step using successive powers of two. -/
theorem S_DIR_L2_DYADIC_KERNEL_STEP
    (r : ℝ) (hr : 0 < r) (j : ℕ) :
    dyadicKernelTerm r j ≤
      (4 / r) * (dyadicPotential r (j + 1) - dyadicPotential r j) := by
  have hq : 0 < (2 : ℝ) ^ j := by positivity
  simpa [dyadicKernelTerm, dyadicPotential, pow_succ, mul_comm] using
    S_DIR_L2_DYADIC_KERNEL_TELESCOPIC_STEP
      r ((2 : ℝ) ^ j) hr hq

/-- Every finite dyadic prefix admits the uniform Schur `4/r` bound. -/
theorem S_DIR_L2_DYADIC_KERNEL_PREFIX_BOUND
    (r : ℝ) (hr : 0 < r) (N : ℕ) :
    (∑ j ∈ Finset.range N, dyadicKernelTerm r j) ≤ 4 / r := by
  have hpartial (n : ℕ) :
      (∑ j ∈ Finset.range n, dyadicKernelTerm r j) ≤
        (4 / r) * (dyadicPotential r n - dyadicPotential r 0) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      calc
        (∑ j ∈ Finset.range n, dyadicKernelTerm r j) +
            dyadicKernelTerm r n
            ≤ (4 / r) * (dyadicPotential r n - dyadicPotential r 0) +
              (4 / r) * (dyadicPotential r (n + 1) - dyadicPotential r n) :=
                add_le_add ih (S_DIR_L2_DYADIC_KERNEL_STEP r hr n)
        _ = (4 / r) *
              (dyadicPotential r (n + 1) - dyadicPotential r 0) := by ring
  have hnonneg0 : 0 ≤ dyadicPotential r 0 := by
    unfold dyadicPotential
    positivity
  have hupper : dyadicPotential r N ≤ 1 := by
    unfold dyadicPotential
    have hden : 0 < r + (2 : ℝ) ^ N := by positivity
    apply (div_le_iff₀ hden).2
    linarith
  have hdiff : dyadicPotential r N - dyadicPotential r 0 ≤ 1 := by
    linarith
  have hfactor : 0 ≤ 4 / r := by positivity
  exact (hpartial N).trans (by
    calc
      (4 / r) * (dyadicPotential r N - dyadicPotential r 0)
          ≤ (4 / r) * 1 := mul_le_mul_of_nonneg_left hdiff hfactor
      _ = 4 / r := mul_one _)

/-- The stronger dyadic constant implies the originally frozen Serrin constant. -/
theorem S_DIR_L2_DYADIC_SERRIN_CONSTANT_LE_FROZEN
    (ν : ℝ) (hν : 0 < ν) :
    16 / (Real.pi ^ 2 * ν) ≤
      45 / (8 * Real.pi * ν) := by
  have hp : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hpi : 0 < Real.pi := Real.pi_pos
  have hb : (128 : ℝ) ≤ 45 * Real.pi := by nlinarith
  have hprod := mul_le_mul_of_nonneg_right hb
    (mul_nonneg hpi.le hν.le)
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  nlinarith [hprod]

end SDirL2
