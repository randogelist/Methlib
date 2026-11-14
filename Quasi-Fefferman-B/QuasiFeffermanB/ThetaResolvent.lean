import QuasiFeffermanB.ThetaLattice
import SingularClosure.PeriodicPoincare

/-! Finite lattice resolvent estimates by two scalar Laplace integrations. -/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory
open scoped BigOperators

namespace QuasiFeffermanB
open SingularClosure
noncomputable section

theorem cutoff_frequency_square_pos {N : ℕ} {k : Frequency}
    (hk : k ∈ cutoffModes N) : 0 < (galerkinFreqSq k : ℝ) := by
  have hge : (1 : ℝ) ≤ (galerkinFreqSq k : ℝ) := by
    exact_mod_cast galerkinFreqSq_ge_one_of_mem hk
  linarith

private theorem positive_exponential_tail_integral (a t : ℝ) (ha : 0 < a) :
    (∫ s : ℝ in Ioi t, Real.exp (-a * s)) = Real.exp (-a * t) / a := by
  rw [integral_exp_mul_Ioi (neg_lt_zero.mpr ha)]
  simp only [neg_div_neg_eq]

/-- First Laplace integration of the finite Gaussian envelope. -/
theorem FINITE_LATTICE_HEAT_RESOLVENT
    (N : ℕ) (t : ℝ) (ht : 0 < t) :
    (∑ k ∈ cutoffModes N,
      Real.exp (-(Real.pi * (galerkinFreqSq k : ℝ)) * t) / (galerkinFreqSq k : ℝ)) ≤
      2 * Real.pi * t ^ (-1 / 2 : ℝ) := by
  let F : Frequency → ℝ → ℝ := fun k s =>
    Real.exp (-(Real.pi * (galerkinFreqSq k : ℝ)) * s)
  have hFi : ∀ k ∈ cutoffModes N, IntegrableOn (F k) (Ioi t) := by
    intro k hk
    exact integrableOn_exp_mul_Ioi
      (neg_lt_zero.mpr (mul_pos Real.pi_pos (cutoff_frequency_square_pos hk))) t
  have hsumI : IntegrableOn (fun s => ∑ k ∈ cutoffModes N, F k s) (Ioi t) :=
    integrable_finsetSum _ hFi
  have hpowI : IntegrableOn (fun s : ℝ => s ^ (-3 / 2 : ℝ)) (Ioi t) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) ht
  have hmono := setIntegral_mono_on hsumI hpowI measurableSet_Ioi
    (fun s hs => (show (∑ k ∈ cutoffModes N, F k s) ≤ s ^ (-3 / 2 : ℝ) from by
      convert FINITE_LATTICE_GAUSSIAN_ENVELOPE N s (ht.trans hs) using 1
      apply Finset.sum_congr rfl
      intro k hk
      dsimp [F]
      congr 1
      ring))
  have hsumEq :
      (∫ s : ℝ in Ioi t, ∑ k ∈ cutoffModes N, F k s) =
      (1 / Real.pi) * ∑ k ∈ cutoffModes N,
        Real.exp (-(Real.pi * (galerkinFreqSq k : ℝ)) * t) / (galerkinFreqSq k : ℝ) := by
    rw [integral_finsetSum _ hFi, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    dsimp [F]
    rw [positive_exponential_tail_integral _ _
      (mul_pos Real.pi_pos (cutoff_frequency_square_pos hk))]
    field_simp [Real.pi_ne_zero, ne_of_gt (cutoff_frequency_square_pos hk)]
    <;> ring
  have hpowEq : (∫ s : ℝ in Ioi t, s ^ (-3 / 2 : ℝ)) = 2 * t ^ (-1 / 2 : ℝ) := by
    rw [integral_Ioi_rpow_of_lt (by norm_num : (-3 / 2 : ℝ) < -1) ht]
    norm_num <;> ring
  rw [hsumEq, hpowEq] at hmono
  have hmul := mul_le_mul_of_nonneg_left hmono Real.pi_pos.le
  have hcancel : Real.pi * ((1 / Real.pi) *
      ∑ k ∈ cutoffModes N,
        Real.exp (-(Real.pi * (galerkinFreqSq k : ℝ)) * t) / (galerkinFreqSq k : ℝ)) =
      ∑ k ∈ cutoffModes N,
        Real.exp (-(Real.pi * (galerkinFreqSq k : ℝ)) * t) / (galerkinFreqSq k : ℝ) := by
    rw [← mul_assoc, mul_one_div_cancel Real.pi_ne_zero, one_mul]
  rw [hcancel] at hmul
  nlinarith

/-- Exact Gamma(1/2) normalization for the second Laplace integration. -/
theorem NORMALIZED_GAUSSIAN_HALF_INTEGRAL (r : ℝ) (hr : 0 < r) :
    (∫ t : ℝ in Ioi 0, t ^ (-1 / 2 : ℝ) * Real.exp (-(Real.pi * r ^ 2 * t))) =
      1 / r := by
  have ha : (0 : ℝ) < 1 / 2 := by norm_num
  have hb : 0 < Real.pi * r ^ 2 := mul_pos Real.pi_pos (sq_pos_of_pos hr)
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi ha hb
  have hval : (1 / (Real.pi * r ^ 2)) ^ (1 / 2 : ℝ) * Real.Gamma (1 / 2) = 1 / r := by
    rw [← Real.sqrt_eq_rpow, Real.Gamma_one_half_eq,
      Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one,
      Real.sqrt_mul Real.pi_pos.le, Real.sqrt_sq hr.le]
    field_simp [ne_of_gt hr, ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos)]
  norm_num only [show (1 / 2 : ℝ) - 1 = -1 / 2 by norm_num] at h
  simpa only [neg_div] using h.trans hval

/-- The exact finite lattice row bound needed by the weighted Schur test.
Only finite-sum integration is used; no infinite Fourier quadratic form is
introduced. -/
theorem FINITE_LATTICE_RESOLVENT_BOUND (N : ℕ) (r : ℝ) (hr : 0 < r) :
    (∑ k ∈ cutoffModes N,
      1 / ((galerkinFreqSq k : ℝ) * (r ^ 2 + (galerkinFreqSq k : ℝ)))) ≤
      2 * Real.pi ^ 2 / r := by
  let G : Frequency → ℝ → ℝ := fun k t =>
    Real.exp (-(Real.pi * (r ^ 2 + (galerkinFreqSq k : ℝ))) * t) /
      (galerkinFreqSq k : ℝ)
  let H : ℝ → ℝ := fun t => t ^ (-1 / 2 : ℝ) * Real.exp (-(Real.pi * r ^ 2 * t))
  have hb : ∀ k ∈ cutoffModes N, 0 < r ^ 2 + (galerkinFreqSq k : ℝ) := by
    intro k hk
    exact add_pos (sq_pos_of_pos hr) (cutoff_frequency_square_pos hk)
  have hGi : ∀ k ∈ cutoffModes N, IntegrableOn (G k) (Ioi 0) := by
    intro k hk
    exact (integrableOn_exp_mul_Ioi
      (neg_lt_zero.mpr (mul_pos Real.pi_pos (hb k hk))) 0).div_const _
  have hsumI : IntegrableOn (fun t => ∑ k ∈ cutoffModes N, G k t) (Ioi 0) :=
    integrable_finsetSum _ hGi
  have hHint : (∫ t : ℝ in Ioi 0, H t) = 1 / r :=
    NORMALIZED_GAUSSIAN_HALF_INTEGRAL r hr
  have hHi : IntegrableOn H (Ioi 0) :=
    Integrable.of_integral_ne_zero (by rw [hHint]; exact one_div_ne_zero (ne_of_gt hr))
  have hmono := setIntegral_mono_on hsumI (hHi.const_mul (2 * Real.pi)) measurableSet_Ioi
    (fun t ht => (show (∑ k ∈ cutoffModes N, G k t) ≤ (2 * Real.pi) * H t from by
      have hheat := FINITE_LATTICE_HEAT_RESOLVENT N t ht
      have heq : (∑ k ∈ cutoffModes N, G k t) =
          Real.exp (-(Real.pi * r ^ 2 * t)) *
            ∑ k ∈ cutoffModes N,
              Real.exp (-(Real.pi * (galerkinFreqSq k : ℝ)) * t) / (galerkinFreqSq k : ℝ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        dsimp [G]
        rw [← mul_div_assoc, ← Real.exp_add]
        congr 2 <;> ring
      rw [heq]
      have hm := mul_le_mul_of_nonneg_left hheat (Real.exp_pos (-(Real.pi * r ^ 2 * t))).le
      dsimp [H]
      nlinarith))
  have hsumEq : (∫ t : ℝ in Ioi 0, ∑ k ∈ cutoffModes N, G k t) =
      (1 / Real.pi) * ∑ k ∈ cutoffModes N,
        1 / ((galerkinFreqSq k : ℝ) * (r ^ 2 + (galerkinFreqSq k : ℝ))) := by
    rw [integral_finsetSum _ hGi, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    dsimp [G]
    rw [integral_div, positive_exponential_tail_integral _ _
      (mul_pos Real.pi_pos (hb k hk))]
    simp only [mul_zero, Real.exp_zero]
    field_simp [Real.pi_ne_zero, ne_of_gt (cutoff_frequency_square_pos hk), ne_of_gt (hb k hk)]
    <;> ring
  rw [hsumEq, integral_const_mul, hHint] at hmono
  have hmul := mul_le_mul_of_nonneg_left hmono Real.pi_pos.le
  have hcancel : Real.pi * ((1 / Real.pi) *
      ∑ k ∈ cutoffModes N,
        1 / ((galerkinFreqSq k : ℝ) * (r ^ 2 + (galerkinFreqSq k : ℝ)))) =
      ∑ k ∈ cutoffModes N,
        1 / ((galerkinFreqSq k : ℝ) * (r ^ 2 + (galerkinFreqSq k : ℝ))) := by
    rw [← mul_assoc, mul_one_div_cancel Real.pi_ne_zero, one_mul]
  rw [hcancel] at hmul
  calc
    _ ≤ Real.pi * ((2 * Real.pi) * (1 / r)) := hmul
    _ = 2 * Real.pi ^ 2 / r := by ring

end
end QuasiFeffermanB
