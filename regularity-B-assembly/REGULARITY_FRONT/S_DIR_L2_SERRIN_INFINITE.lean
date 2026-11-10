import S_DIR_L2_SERRIN_FINITE
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

set_option autoImplicit false
set_option maxHeartbeats 0

open MeasureTheory
open scoped BigOperators

noncomputable section

namespace SDirL2

/-!
# S_DIR_L2 v0.9.0 — infinite-mode Serrin time-majorant

This module passes from the previously A-tiered finite Fourier heat bound
through monotone convergence of nonnegative Lebesgue integrals. Its primary
endpoint is the infinite monotone supremum of finite heat-amplitude squares.

This is an unconditional theorem for EVERY monotone finite-mode sequence.
The separate identification of an exhaustive sequence with the full Fourier
series, and physical torus synthesis and Leray–Hopf uniqueness, remain open.
-/

/-- Every finite absolute Fourier heat amplitude is pointwise nonnegative,
    irrespective of the time parameter. -/
theorem S_DIR_L2_FINITE_HEAT_AMPLITUDE_NONNEG
    {ι : Type*} (F : Finset ι) (r b : ι → ℝ)
    (κ t : ℝ) (hb : ∀ k, 0 ≤ b k) :
    0 ≤ finiteHeatAmplitude F r b κ t := by
  unfold finiteHeatAmplitude
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (hb i) (Real.exp_nonneg _)

/-- Nonnegative finite heat amplitudes increase under inclusion of
    Fourier frequency truncations. -/
theorem S_DIR_L2_FINITE_HEAT_AMPLITUDE_MONO
    {ι : Type*} (F G : Finset ι) (hFG : F ⊆ G)
    (r b : ι → ℝ) (κ t : ℝ) (hb : ∀ k, 0 ≤ b k) :
    finiteHeatAmplitude F r b κ t ≤
      finiteHeatAmplitude G r b κ t := by
  unfold finiteHeatAmplitude
  apply Finset.sum_le_sum_of_subset_of_nonneg hFG
  intro i hi hnot
  exact mul_nonneg (hb i) (Real.exp_nonneg _)

/-- Every finite heat-amplitude square is integrable over positive time.
    The proof is a finite sum of exponentially integrable heat pairs. -/
theorem S_DIR_L2_FINITE_HEAT_SQUARE_INTEGRABLE
    {ι : Type*} [DecidableEq ι]
    (F : Finset ι) (r b : ι → ℝ) (κ : ℝ)
    (hκ : 0 < κ) (hr : ∀ i, 0 < r i) :
    IntegrableOn
      (fun t : ℝ => (finiteHeatAmplitude F r b κ t) ^ 2)
      (Set.Ioi (0 : ℝ)) := by
  classical
  have hinner (i : ι) :
      IntegrableOn (fun t : ℝ => ∑ j ∈ F,
        (b i * b j) *
          Real.exp (-(κ * (r i ^ 2 + r j ^ 2) * t)))
        (Set.Ioi (0 : ℝ)) := by
    apply integrable_finset_sum
    intro j hj
    exact S_DIR_L2_FINITE_HEAT_PAIR_INTEGRABLE r b κ hκ hr i j
  have houter :
      IntegrableOn (fun t : ℝ => ∑ i ∈ F, ∑ j ∈ F,
        (b i * b j) *
          Real.exp (-(κ * (r i ^ 2 + r j ^ 2) * t)))
        (Set.Ioi (0 : ℝ)) := by
    apply integrable_finset_sum
    intro i hi
    exact hinner i
  simpa only [S_DIR_L2_FINITE_HEAT_AMPLITUDE_SQUARE] using houter

/-- Monotone convergence for nonnegative square-amplitude trajectories.
    An arbitrary monotone sequence of finite approximations is permitted.
    No pointwise existence of a real infinite Fourier sum is presupposed. -/
theorem S_DIR_L2_GENERIC_MONOTONE_L2_LINTEGRAL
    (g : ℕ → ℝ → ℝ) (C : ℝ)
    (hgm : ∀ n, Measurable (g n))
    (hgn : ∀ n t, 0 ≤ g n t)
    (hgmono : ∀ n m, n ≤ m → ∀ t, g n t ≤ g m t)
    (hgint : ∀ n, IntegrableOn (fun t => (g n t) ^ 2)
      (Set.Ioi (0 : ℝ)))
    (hgbound : ∀ n,
      (∫ t : ℝ in Set.Ioi (0 : ℝ), (g n t) ^ 2) ≤ C) :
    (∫⁻ t : ℝ in Set.Ioi (0 : ℝ),
      ⨆ n : ℕ, ENNReal.ofReal ((g n t) ^ 2)) ≤ ENNReal.ofReal C := by
  have hmeas (n : ℕ) :
      Measurable (fun t : ℝ => ENNReal.ofReal ((g n t) ^ 2)) :=
    ENNReal.measurable_ofReal.comp ((hgm n).pow_const 2)
  have hmono :
      Monotone (fun n : ℕ =>
        (fun t : ℝ => ENNReal.ofReal ((g n t) ^ 2))) := by
    intro n m hnm t
    apply ENNReal.ofReal_le_ofReal
    have h1 := hgn n t
    have h2 := hgn m t
    have h3 := hgmono n m hnm t
    nlinarith [sq_nonneg (g n t), sq_nonneg (g m t)]
  rw [lintegral_iSup hmeas hmono]
  refine iSup_le fun n => ?_
  rw [← ofReal_integral_eq_lintegral_ofReal (hgint n)
    (Filter.Eventually.of_forall (fun t => sq_nonneg (g n t)))]
  exact ENNReal.ofReal_le_ofReal (hgbound n)

/-- The unconditional v0.9.0 infinite-mode Serrin majorant.

For EVERY monotone family of finite subsets of the actual directional
plane, the square of the supremum heat amplitude has a finite nonnegative
Lebesgue integral bounded by 16/(pi^2 nu) times the complete L2 coefficient
mass. No exhaustion assumption is needed for this stronger universal bound.
-/
theorem S_DIR_L2_INFINITE_SERRIN_HEAT
    (a : Mode3) (ha : a ≠ 0)
    (ν : ℝ) (hν : 0 < ν)
    (F : ℕ → Finset (ActivePlaneMode a))
    (hF : Monotone F)
    (z : ActivePlaneMode a → ℂ)
    (hz : Summable (fun k => ‖z k‖ ^ 2)) :
    (∫⁻ t : ℝ in Set.Ioi (0 : ℝ),
      ⨆ n : ℕ, ENNReal.ofReal
        ((finiteHeatAmplitude (F n) (activeRadius a)
            (fun k => ‖z k‖) (4 * Real.pi ^ 2 * ν) t) ^ 2)) ≤
      ENNReal.ofReal
        ((16 / (Real.pi ^ 2 * ν)) *
          (∑' k : ActivePlaneMode a, ‖z k‖ ^ 2)) := by
  classical
  have hκ : 0 < 4 * Real.pi ^ 2 * ν := by positivity
  have hC : 0 ≤ 16 / (Real.pi ^ 2 * ν) := by positivity
  apply S_DIR_L2_GENERIC_MONOTONE_L2_LINTEGRAL
    (fun n t => finiteHeatAmplitude (F n) (activeRadius a)
      (fun k => ‖z k‖) (4 * Real.pi ^ 2 * ν) t)
    ((16 / (Real.pi ^ 2 * ν)) *
      (∑' k : ActivePlaneMode a, ‖z k‖ ^ 2))
  · intro n
    unfold finiteHeatAmplitude
    fun_prop
  · intro n t
    exact S_DIR_L2_FINITE_HEAT_AMPLITUDE_NONNEG
      (F n) (activeRadius a) (fun k => ‖z k‖)
      (4 * Real.pi ^ 2 * ν) t (fun k => norm_nonneg _)
  · intro n m hnm t
    exact S_DIR_L2_FINITE_HEAT_AMPLITUDE_MONO
      (F n) (F m) (hF hnm)
      (activeRadius a) (fun k => ‖z k‖)
      (4 * Real.pi ^ 2 * ν) t (fun k => norm_nonneg _)
  · intro n
    exact S_DIR_L2_FINITE_HEAT_SQUARE_INTEGRABLE
      (F n) (activeRadius a) (fun k => ‖z k‖)
      (4 * Real.pi ^ 2 * ν) hκ
      (fun k => S_DIR_L2_ACTIVE_RADIUS_POS a k)
  · intro n
    calc
      (∫ t : ℝ in Set.Ioi (0 : ℝ),
        (finiteHeatAmplitude (F n) (activeRadius a)
            (fun k => ‖z k‖) (4 * Real.pi ^ 2 * ν) t) ^ 2)
          ≤ (16 / (Real.pi ^ 2 * ν)) *
              ∑ k ∈ F n, ‖z k‖ ^ 2 :=
          S_DIR_L2_FINITE_SERRIN_HEAT_ESTIMATE a ha ν hν (F n) z
      _ ≤ (16 / (Real.pi ^ 2 * ν)) *
              (∑' k : ActivePlaneMode a, ‖z k‖ ^ 2) := by
        exact mul_le_mul_of_nonneg_left
          (Summable.sum_le_tsum (F n)
            (fun k hk => sq_nonneg (‖z k‖)) hz) hC

/-- The original frozen Serrin constant follows from the improved
    dyadic bound, without altering the root theorem. -/
theorem S_DIR_L2_INFINITE_SERRIN_FROZEN_MAJORANT
    (a : Mode3) (ha : a ≠ 0)
    (ν : ℝ) (hν : 0 < ν)
    (F : ℕ → Finset (ActivePlaneMode a))
    (hF : Monotone F)
    (z : ActivePlaneMode a → ℂ)
    (hz : Summable (fun k => ‖z k‖ ^ 2)) :
    (∫⁻ t : ℝ in Set.Ioi (0 : ℝ),
      ⨆ n : ℕ, ENNReal.ofReal
        ((finiteHeatAmplitude (F n) (activeRadius a)
            (fun k => ‖z k‖) (4 * Real.pi ^ 2 * ν) t) ^ 2)) ≤
      ENNReal.ofReal
        ((45 / (8 * Real.pi * ν)) *
          (∑' k : ActivePlaneMode a, ‖z k‖ ^ 2)) := by
  have hsum :
      0 ≤ (∑' k : ActivePlaneMode a, ‖z k‖ ^ 2) :=
    tsum_nonneg (fun k => sq_nonneg (‖z k‖))
  calc
    (∫⁻ t : ℝ in Set.Ioi (0 : ℝ),
      ⨆ n : ℕ, ENNReal.ofReal
        ((finiteHeatAmplitude (F n) (activeRadius a)
            (fun k => ‖z k‖) (4 * Real.pi ^ 2 * ν) t) ^ 2))
        ≤ ENNReal.ofReal
          ((16 / (Real.pi ^ 2 * ν)) *
            (∑' k : ActivePlaneMode a, ‖z k‖ ^ 2)) :=
          S_DIR_L2_INFINITE_SERRIN_HEAT a ha ν hν F hF z hz
    _ ≤ ENNReal.ofReal
          ((45 / (8 * Real.pi * ν)) *
            (∑' k : ActivePlaneMode a, ‖z k‖ ^ 2)) := by
        apply ENNReal.ofReal_le_ofReal
        exact mul_le_mul_of_nonneg_right
          (S_DIR_L2_DYADIC_SERRIN_CONSTANT_LE_FROZEN ν hν) hsum

end SDirL2
