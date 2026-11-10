import S_DIR_L2_INFINITE_SCHUR
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

set_option autoImplicit false
set_option maxHeartbeats 0

open MeasureTheory
open scoped BigOperators

noncomputable section

namespace SDirL2

/-!
# S_DIR_L2 v0.8.0: physical-time Laplace and finite Serrin heat certificate

This module introduces a REAL integral over `(0,+infinity)` and derives
its exact finite Fourier heat-kernel formula and unconditional finite
Serrin estimate. It uses the previously verified actual-plane Schur
bound. This is not yet infinite physical torus Fourier synthesis, and
it does not assert unrestricted Leray--Hopf uniqueness.
-/

/-- Positivity and integrability of the decaying exponential on `(0,+infinity)`. -/
theorem S_DIR_L2_EXPONENTIAL_INTEGRABLE_ON_Ioi
    (c : ℝ) (hc : 0 < c) :
    IntegrableOn (fun t : ℝ => Real.exp (-(c * t))) (Set.Ioi (0 : ℝ)) := by
  have hneg : -c < 0 := by linarith
  simpa only [neg_mul] using
    (integrableOn_exp_mul_Ioi (a := -c) hneg (0 : ℝ))

/-- Exact Laplace transform of a positive-rate exponential on `(0,+infinity)`. -/
theorem S_DIR_L2_EXPONENTIAL_INTEGRAL_ON_Ioi
    (c : ℝ) (hc : 0 < c) :
    (∫ t : ℝ in Set.Ioi (0 : ℝ), Real.exp (-(c * t))) = 1 / c := by
  have hneg : -c < 0 := by linarith
  have h := integral_exp_mul_Ioi (a := -c) hneg (0 : ℝ)
  calc
    (∫ t : ℝ in Set.Ioi (0 : ℝ), Real.exp (-(c * t)))
        = -(Real.exp ((-c) * 0)) / (-c) := by
            simpa only [neg_mul] using h
    _ = 1 / c := by simp

/-- Two decaying heat modes multiply into the exponential of the sum of
    their positive spectral rates. -/
theorem S_DIR_L2_TWO_HEAT_MULTIPLIERS
    (κ x y t : ℝ) :
    Real.exp (-(κ * x ^ 2 * t)) * Real.exp (-(κ * y ^ 2 * t)) =
      Real.exp (-(κ * (x ^ 2 + y ^ 2) * t)) := by
  rw [← Real.exp_add]
  congr 1
  ring

/-- The exact integral of two heat modes is the Schur kernel, divided
    by the positive diffusion coefficient. -/
theorem S_DIR_L2_HEAT_PAIR_TIME_INTEGRAL
    (κ x y : ℝ) (hκ : 0 < κ) (hx : 0 < x) (hy : 0 < y) :
    (∫ t : ℝ in Set.Ioi (0 : ℝ),
        Real.exp (-(κ * x ^ 2 * t)) * Real.exp (-(κ * y ^ 2 * t))) =
      κ⁻¹ * (x ^ 2 + y ^ 2)⁻¹ := by
  have hsum : 0 < x ^ 2 + y ^ 2 := by positivity
  have hc : 0 < κ * (x ^ 2 + y ^ 2) := mul_pos hκ hsum
  calc
    (∫ t : ℝ in Set.Ioi (0 : ℝ),
        Real.exp (-(κ * x ^ 2 * t)) * Real.exp (-(κ * y ^ 2 * t)))
        = (∫ t : ℝ in Set.Ioi (0 : ℝ),
            Real.exp (-((κ * (x ^ 2 + y ^ 2)) * t))) := by
              congr 1
              funext t
              exact S_DIR_L2_TWO_HEAT_MULTIPLIERS κ x y t
    _ = 1 / (κ * (x ^ 2 + y ^ 2)) :=
      S_DIR_L2_EXPONENTIAL_INTEGRAL_ON_Ioi _ hc
    _ = κ⁻¹ * (x ^ 2 + y ^ 2)⁻¹ := by
      calc
        1 / (κ * (x ^ 2 + y ^ 2)) =
            (x ^ 2 + y ^ 2)⁻¹ * κ⁻¹ := by
              rw [one_div, mul_inv_rev]
        _ = κ⁻¹ * (x ^ 2 + y ^ 2)⁻¹ := mul_comm _ _

/-- Finite nonnegative absolute-Fourier heat amplitude. -/
def finiteHeatAmplitude
    {ι : Type*} (F : Finset ι) (r b : ι → ℝ)
    (κ t : ℝ) : ℝ :=
  ∑ i ∈ F, b i * Real.exp (-(κ * r i ^ 2 * t))

/-- Algebraic expansion of the squared amplitude, with no analytic
    assumptions. -/
theorem S_DIR_L2_FINITE_HEAT_AMPLITUDE_SQUARE
    {ι : Type*} (F : Finset ι) (r b : ι → ℝ)
    (κ t : ℝ) :
    (finiteHeatAmplitude F r b κ t) ^ 2 =
      ∑ i ∈ F, ∑ j ∈ F,
        (b i * b j) * Real.exp (-(κ * (r i ^ 2 + r j ^ 2) * t)) := by
  classical
  unfold finiteHeatAmplitude
  calc
    (∑ i ∈ F, b i * Real.exp (-(κ * r i ^ 2 * t))) ^ 2 =
        (∑ i ∈ F, b i * Real.exp (-(κ * r i ^ 2 * t))) *
        (∑ j ∈ F, b j * Real.exp (-(κ * r j ^ 2 * t))) := by ring
    _ = ∑ i ∈ F, ∑ j ∈ F,
        (b i * Real.exp (-(κ * r i ^ 2 * t))) *
        (b j * Real.exp (-(κ * r j ^ 2 * t))) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.mul_sum]
    _ = ∑ i ∈ F, ∑ j ∈ F,
        (b i * b j) * Real.exp (-(κ * (r i ^ 2 + r j ^ 2) * t)) := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          rw [← S_DIR_L2_TWO_HEAT_MULTIPLIERS κ (r i) (r j) t]
          ring

/-- Each pair contribution is integrable from the rough initial trace. -/
theorem S_DIR_L2_FINITE_HEAT_PAIR_INTEGRABLE
    {ι : Type*} (r b : ι → ℝ) (κ : ℝ)
    (hκ : 0 < κ) (hr : ∀ i, 0 < r i) (i j : ι) :
    IntegrableOn
      (fun t : ℝ => (b i * b j) *
        Real.exp (-(κ * (r i ^ 2 + r j ^ 2) * t)))
      (Set.Ioi (0 : ℝ)) := by
  have hsum : 0 < r i ^ 2 + r j ^ 2 := by
    have hi := hr i
    have hj := hr j
    positivity
  have hc : 0 < κ * (r i ^ 2 + r j ^ 2) := mul_pos hκ hsum
  exact (S_DIR_L2_EXPONENTIAL_INTEGRABLE_ON_Ioi _ hc).const_mul (b i * b j)

/-- Exact integral of each pair, including the Fourier coefficient weights. -/
theorem S_DIR_L2_FINITE_HEAT_PAIR_WEIGHTED_INTEGRAL
    {ι : Type*} (r b : ι → ℝ) (κ : ℝ)
    (hκ : 0 < κ) (hr : ∀ i, 0 < r i) (i j : ι) :
    (∫ t : ℝ in Set.Ioi (0 : ℝ),
        (b i * b j) *
        Real.exp (-(κ * (r i ^ 2 + r j ^ 2) * t))) =
      κ⁻¹ * (abstractHeatKernel r i j * b i * b j) := by
  have hsum : 0 < r i ^ 2 + r j ^ 2 := by
    have hi := hr i
    have hj := hr j
    positivity
  have hc : 0 < κ * (r i ^ 2 + r j ^ 2) := mul_pos hκ hsum
  calc
    (∫ t : ℝ in Set.Ioi (0 : ℝ),
        (b i * b j) *
        Real.exp (-(κ * (r i ^ 2 + r j ^ 2) * t))) =
      (b i * b j) *
        (∫ t : ℝ in Set.Ioi (0 : ℝ),
          Real.exp (-((κ * (r i ^ 2 + r j ^ 2)) * t))) := by
            rw [MeasureTheory.integral_const_mul]
    _ = (b i * b j) * (1 / (κ * (r i ^ 2 + r j ^ 2))) := by
      rw [S_DIR_L2_EXPONENTIAL_INTEGRAL_ON_Ioi _ hc]
    _ = κ⁻¹ * (abstractHeatKernel r i j * b i * b j) := by
      unfold abstractHeatKernel
      simp [div_eq_mul_inv, mul_inv_rev]
      ring

/-- Exact finite-mode time-integrated absolute heat energy identity. -/
theorem S_DIR_L2_FINITE_HEAT_ENERGY_INTEGRAL
    {ι : Type*} [DecidableEq ι]
    (F : Finset ι) (r b : ι → ℝ) (κ : ℝ)
    (hκ : 0 < κ) (hr : ∀ i, 0 < r i) :
    (∫ t : ℝ in Set.Ioi (0 : ℝ),
        (finiteHeatAmplitude F r b κ t) ^ 2) =
      κ⁻¹ * (∑ i ∈ F, ∑ j ∈ F,
        abstractHeatKernel r i j * b i * b j) := by
  classical
  have hint (i : ι) :
      IntegrableOn (fun t : ℝ => ∑ j ∈ F,
        (b i * b j) *
        Real.exp (-(κ * (r i ^ 2 + r j ^ 2) * t)))
        (Set.Ioi (0 : ℝ)) := by
    apply integrable_finset_sum
    intro j hj
    exact S_DIR_L2_FINITE_HEAT_PAIR_INTEGRABLE r b κ hκ hr i j
  calc
    (∫ t : ℝ in Set.Ioi (0 : ℝ),
        (finiteHeatAmplitude F r b κ t) ^ 2) =
      (∫ t : ℝ in Set.Ioi (0 : ℝ),
          ∑ i ∈ F, ∑ j ∈ F,
            (b i * b j) *
            Real.exp (-(κ * (r i ^ 2 + r j ^ 2) * t))) := by
              congr 1
              funext t
              exact S_DIR_L2_FINITE_HEAT_AMPLITUDE_SQUARE F r b κ t
    _ = ∑ i ∈ F, ∑ j ∈ F,
        (∫ t : ℝ in Set.Ioi (0 : ℝ),
          (b i * b j) *
          Real.exp (-(κ * (r i ^ 2 + r j ^ 2) * t))) := by
            rw [integral_finset_sum]
            · apply Finset.sum_congr rfl
              intro i hi
              rw [integral_finset_sum]
              intro j hj
              exact S_DIR_L2_FINITE_HEAT_PAIR_INTEGRABLE r b κ hκ hr i j
            · intro i hi
              exact hint i
    _ = ∑ i ∈ F, ∑ j ∈ F,
        κ⁻¹ * (abstractHeatKernel r i j * b i * b j) := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          exact S_DIR_L2_FINITE_HEAT_PAIR_WEIGHTED_INTEGRAL r b κ hκ hr i j
    _ = κ⁻¹ * (∑ i ∈ F, ∑ j ∈ F,
        abstractHeatKernel r i j * b i * b j) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.mul_sum]

/-- Unconditional, finite-mode time-integrated Serrin majorant on the
    actual nonzero integer-direction Fourier plane. -/
theorem S_DIR_L2_FINITE_SERRIN_HEAT_ESTIMATE
    (a : Mode3) (ha : a ≠ 0) (ν : ℝ) (hν : 0 < ν)
    (F : Finset (ActivePlaneMode a))
    (z : ActivePlaneMode a → ℂ) :
    (∫ t : ℝ in Set.Ioi (0 : ℝ),
      (finiteHeatAmplitude F (activeRadius a) (fun k => ‖z k‖)
          (4 * Real.pi ^ 2 * ν) t) ^ 2) ≤
      (16 / (Real.pi ^ 2 * ν)) * ∑ k ∈ F, ‖z k‖ ^ 2 := by
  classical
  have hκ : 0 < 4 * Real.pi ^ 2 * ν := by positivity
  have hintegral := S_DIR_L2_FINITE_HEAT_ENERGY_INTEGRAL
    F (activeRadius a) (fun k => ‖z k‖)
    (4 * Real.pi ^ 2 * ν) hκ
    (fun k => S_DIR_L2_ACTIVE_RADIUS_POS a k)
  have hschur := S_DIR_L2_ACTIVE_FINITE_HEAT_SCHUR
    a ha F (fun k => ‖z k‖)
  have hnormal :
      (4 * Real.pi ^ 2 * ν)⁻¹ * 64 =
        16 / (Real.pi ^ 2 * ν) := by
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    have hv : ν ≠ 0 := ne_of_gt hν
    field_simp [hpi, hv]
    ring
  calc
    (∫ t : ℝ in Set.Ioi (0 : ℝ),
      (finiteHeatAmplitude F (activeRadius a) (fun k => ‖z k‖)
          (4 * Real.pi ^ 2 * ν) t) ^ 2) =
        (4 * Real.pi ^ 2 * ν)⁻¹ *
          (∑ i ∈ F, ∑ j ∈ F,
            abstractHeatKernel (activeRadius a) i j * ‖z i‖ * ‖z j‖) :=
            hintegral
    _ ≤ (4 * Real.pi ^ 2 * ν)⁻¹ *
          (64 * ∑ k ∈ F, ‖z k‖ ^ 2) := by
            exact mul_le_mul_of_nonneg_left hschur (inv_nonneg.mpr hκ.le)
    _ = (16 / (Real.pi ^ 2 * ν)) * ∑ k ∈ F, ‖z k‖ ^ 2 := by
          rw [← mul_assoc, hnormal]

end SDirL2
