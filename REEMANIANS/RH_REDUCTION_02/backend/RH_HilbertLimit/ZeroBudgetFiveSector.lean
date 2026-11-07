import RH_HilbertLimit.ZeroBudgetSecondSector
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# A narrow actual-zero sector for the first five cancellation checks

A cubic theta envelope gives the rational completed-zeta bound 9/190.
This excludes actual xi zeros through height 17/4, and consequently puts
every canonical node in the cone 4 |im| <= re. The bound is finite-order
analytic information and does not assert RH or all-order admissibility.
Prepared by source inspection only; native compilation and audit are pending.
-/

set_option autoImplicit false
noncomputable section

namespace RH_HilbertLimit

open AngularMaster OverflowResidueRH MeasureTheory Set

private theorem zeroBudget_exp_three_ge_twenty : (20 : ℝ) ≤ Real.exp 3 := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 3) 9
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith

private theorem zeroBudget_exp_three_mul_cubic_lower (x : ℝ) (hx : 1 ≤ x) :
    20 * x ^ 3 ≤ Real.exp (3 * x) := by
  have hxexp : x ≤ Real.exp (x - 1) := by
    have h := Real.add_one_le_exp (x - 1)
    linarith
  have hc := pow_le_pow_left₀ (by linarith : 0 ≤ x) hxexp 3
  calc
    20 * x ^ 3 ≤ Real.exp 3 * Real.exp (x - 1) ^ 3 :=
      mul_le_mul zeroBudget_exp_three_ge_twenty hc (by positivity)
        (Real.exp_nonneg _)
    _ = Real.exp (3 * x) := by
      rw [show 3 * x = 3 + (x - 1) + (x - 1) + (x - 1) by ring,
        Real.exp_add, Real.exp_add, Real.exp_add]
      ring

/-- The literal modified theta kernel has a cubic rational envelope. -/
theorem zeroBudget_thetaKernel_le_inverse_cube (x : ℝ) (hx : 1 ≤ x) :
    ‖hurwitzThetaMellinKernel x‖ ≤ (2 / 19 : ℝ) * x ^ (-3 : ℝ) := by
  have hxpos : 0 < x := by linarith
  have hpi : (3 : ℝ) ≤ Real.pi := Real.pi_gt_three.le
  have hpx : (3 : ℝ) ≤ Real.pi * x := by nlinarith
  have hE : Real.exp (-Real.pi * x) ≤ (1 / 20 : ℝ) := by
    have hnegthree : Real.exp (-3) ≤ (1 / 20 : ℝ) := by
      rw [Real.exp_neg, inv_eq_one_div]
      exact (div_le_iff₀ (Real.exp_pos 3)).2 (by
        nlinarith [zeroBudget_exp_three_ge_twenty])
    exact (Real.exp_le_exp.mpr (by nlinarith : -Real.pi * x ≤ -3)).trans hnegthree
  have hden : 0 < 1 - Real.exp (-Real.pi * x) := by linarith
  have hfrac : 2 / (1 - Real.exp (-Real.pi * x)) ≤ (40 / 19 : ℝ) := by
    apply (div_le_iff₀ hden).2
    linarith
  have hsmall : Real.exp (-Real.pi * x) ≤ 1 / (20 * x ^ 3) := by
    calc
      Real.exp (-Real.pi * x) ≤ Real.exp (-(3 * x)) := by
        apply Real.exp_le_exp.mpr
        nlinarith
      _ = 1 / Real.exp (3 * x) := by rw [Real.exp_neg, inv_eq_one_div]
      _ ≤ 1 / (20 * x ^ 3) :=
        one_div_le_one_div_of_le (by positivity)
          (zeroBudget_exp_three_mul_cubic_lower x hx)
  by_cases hxeq : x = 1
  · subst x
    rw [hurwitzThetaMellinKernel_one, norm_zero]
    positivity
  have hxlt : 1 < x := lt_of_le_of_ne hx (Ne.symm hxeq)
  rw [hurwitzThetaMellinKernel_eq_evenKernel_sub_one hxlt]
  have heven : (HurwitzZeta.evenKernel 0 x : ℂ) =
      jacobiTheta (Complex.I * (x : ℂ)) := by
    simpa [jacobiTheta_eq_jacobiTheta₂] using HurwitzZeta.evenKernel_def 0 x
  rw [Complex.ofReal_sub, Complex.ofReal_one, heven]
  have htheta := norm_jacobiTheta_sub_one_le
    (τ := Complex.I * (x : ℂ)) (by simpa using hxpos)
  simp only [Complex.mul_im, Complex.I_re, Complex.ofReal_im, mul_zero,
    Complex.I_im, Complex.ofReal_re, one_mul, zero_add] at htheta
  calc
    ‖jacobiTheta (Complex.I * (x : ℂ)) - 1‖ ≤
        2 / (1 - Real.exp (-Real.pi * x)) * Real.exp (-Real.pi * x) := htheta
    _ ≤ (40 / 19 : ℝ) * Real.exp (-Real.pi * x) :=
      mul_le_mul_of_nonneg_right hfrac (Real.exp_nonneg _)
    _ ≤ (40 / 19 : ℝ) * (1 / (20 * x ^ 3)) :=
      mul_le_mul_of_nonneg_left hsmall (by norm_num)
    _ = (2 / 19 : ℝ) * x ^ (-3 : ℝ) := by
      rw [Real.rpow_neg hxpos.le]
      norm_num <;> field_simp [hxpos.ne'] <;> ring

/-- Theta inversion transports the cubic envelope below one. -/
theorem zeroBudget_thetaKernel_le_five_halves (x : ℝ)
    (hx : 0 < x) (hxone : x ≤ 1) :
    ‖hurwitzThetaMellinKernel x‖ ≤ (2 / 19 : ℝ) * x ^ (5 / 2 : ℝ) := by
  have hypos : 0 < 1 / x := one_div_pos.mpr hx
  have hyone : 1 ≤ 1 / x := one_le_one_div hx hxone
  have hinv : hurwitzThetaMellinKernel x =
      ((((1 / x) ^ (1 / 2 : ℝ) : ℝ) : ℂ) •
        hurwitzThetaMellinKernel (1 / x)) := by
    simpa [hx.ne'] using hurwitzThetaMellinKernel_inversion (1 / x) hypos
  rw [hinv, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hypos.le _)]
  calc
    (1 / x) ^ (1 / 2 : ℝ) * ‖hurwitzThetaMellinKernel (1 / x)‖ ≤
        (1 / x) ^ (1 / 2 : ℝ) * ((2 / 19 : ℝ) * (1 / x) ^ (-3 : ℝ)) :=
      mul_le_mul_of_nonneg_left (zeroBudget_thetaKernel_le_inverse_cube (1 / x) hyone)
        (Real.rpow_nonneg hypos.le _)
    _ = (2 / 19 : ℝ) * (1 / x) ^ (-(5 / 2 : ℝ)) := by
      rw [mul_left_comm, ← Real.rpow_add hypos]
      norm_num
    _ = (2 / 19 : ℝ) * x ^ (5 / 2 : ℝ) := by
      rw [one_div x, Real.inv_rpow hx.le, ← Real.rpow_neg hx.le, neg_neg]

/-- A rational strip estimate strong enough for the finite fifth row. -/
theorem zeroBudget_completedZeta0_norm_le_nine_190 {s : ℂ}
    (hs0 : 0 ≤ s.re) (hs1 : s.re ≤ 1) :
    ‖completedRiemannZeta₀ s‖ ≤ (9 / 190 : ℝ) := by
  let F : ℝ → ℂ := fun x => (x : ℂ) ^ (s / 2 - 1) • hurwitzThetaMellinKernel x
  have hF_int : IntegrableOn F (Ioi 0) := by
    simpa only [F, MellinConvergent] using hurwitzThetaMellinKernel_convergent (s / 2)
  have hFnorm_full : IntegrableOn (fun x : ℝ => ‖F x‖) (Ioi 0) := hF_int.norm
  have hFnorm (x : ℝ) (hx : 0 < x) :
      ‖F x‖ = x ^ (s.re / 2 - 1) * ‖hurwitzThetaMellinKernel x‖ := by
    dsimp [F]
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
    simp
  have hupper_int : (∫ x : ℝ in Ioi 1, ‖F x‖) ≤ (4 / 95 : ℝ) := by
    have hmajor : IntegrableOn (fun x : ℝ => (2 / 19 : ℝ) * x ^ (-(7 / 2) : ℝ))
        (Ioi 1) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num : (-(7 / 2) : ℝ) < -1)
        (by norm_num : (0 : ℝ) < 1)).const_mul _
    calc
      (∫ x : ℝ in Ioi 1, ‖F x‖) ≤
          ∫ x : ℝ in Ioi 1, (2 / 19 : ℝ) * x ^ (-(7 / 2) : ℝ) := by
        apply setIntegral_mono_on
          (hFnorm_full.mono_set (Ioi_subset_Ioi zero_le_one)) hmajor measurableSet_Ioi
        intro x hx
        have hxpos : 0 < x := zero_lt_one.trans hx
        rw [hFnorm x hxpos]
        have hpow : x ^ (s.re / 2 - 1) ≤ x ^ (-(1 / 2) : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hx.le (by linarith)
        calc
          x ^ (s.re / 2 - 1) * ‖hurwitzThetaMellinKernel x‖ ≤
              x ^ (-(1 / 2) : ℝ) * ‖hurwitzThetaMellinKernel x‖ :=
            mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
          _ ≤ x ^ (-(1 / 2) : ℝ) * ((2 / 19 : ℝ) * x ^ (-3 : ℝ)) :=
            mul_le_mul_of_nonneg_left (zeroBudget_thetaKernel_le_inverse_cube x hx.le)
              (Real.rpow_nonneg hxpos.le _)
          _ = (2 / 19 : ℝ) * x ^ (-(7 / 2) : ℝ) := by
            rw [mul_left_comm, ← Real.rpow_add hxpos]
            norm_num
      _ = (4 / 95 : ℝ) := by
        rw [integral_const_mul,
          integral_Ioi_rpow_of_lt (by norm_num : (-(7 / 2) : ℝ) < -1)
            (by norm_num : (0 : ℝ) < 1)]
        norm_num
  have hlower_int : (∫ x : ℝ in Ioc 0 1, ‖F x‖) ≤ (1 / 19 : ℝ) := by
    have hmajor : IntegrableOn (fun x : ℝ => (2 / 19 : ℝ) * x) (Ioc 0 1) := by
      have hid : IntegrableOn (fun x : ℝ => x) (Icc 0 1) volume :=
        continuous_id.integrableOn_Icc
      have hioc : IntegrableOn (fun x : ℝ => x) (Ioc 0 1) volume :=
        hid.mono_set Ioc_subset_Icc_self
      exact hioc.const_mul (2 / 19 : ℝ)
    calc
      (∫ x : ℝ in Ioc 0 1, ‖F x‖) ≤
          ∫ x : ℝ in Ioc 0 1, (2 / 19 : ℝ) * x := by
        apply setIntegral_mono_on
          (hFnorm_full.mono_set Ioc_subset_Ioi_self) hmajor measurableSet_Ioc
        intro x hx
        rw [hFnorm x hx.1]
        have hpow : x ^ (s.re / 2 + 3 / 2) ≤ x := by
          calc
            x ^ (s.re / 2 + 3 / 2) ≤ x ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_ge hx.1 hx.2 (by linarith)
            _ = x := by simp
        calc
          x ^ (s.re / 2 - 1) * ‖hurwitzThetaMellinKernel x‖ ≤
              x ^ (s.re / 2 - 1) * ((2 / 19 : ℝ) * x ^ (5 / 2 : ℝ)) :=
            mul_le_mul_of_nonneg_left
              (zeroBudget_thetaKernel_le_five_halves x hx.1 hx.2)
              (Real.rpow_nonneg hx.1.le _)
          _ = (2 / 19 : ℝ) * x ^ (s.re / 2 + 3 / 2) := by
            rw [mul_left_comm, ← Real.rpow_add hx.1]
            congr 2 <;> ring
          _ ≤ (2 / 19 : ℝ) * x :=
            mul_le_mul_of_nonneg_left hpow (by norm_num)
      _ = (1 / 19 : ℝ) := by
        rw [integral_const_mul, ← intervalIntegral.integral_of_le zero_le_one]
        norm_num [integral_id]
  have hbound : ‖mellin hurwitzThetaMellinKernel (s / 2)‖ ≤ (9 / 95 : ℝ) := by
    calc
      ‖mellin hurwitzThetaMellinKernel (s / 2)‖ = ‖∫ x : ℝ in Ioi 0, F x‖ := rfl
      _ ≤ ∫ x : ℝ in Ioi 0, ‖F x‖ := norm_integral_le_integral_norm _
      _ = (∫ x : ℝ in Ioc 0 1, ‖F x‖) + ∫ x : ℝ in Ioi 1, ‖F x‖ := by
        rw [← Ioc_union_Ioi_eq_Ioi zero_le_one,
          setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi]
        · exact hFnorm_full.mono_set Ioc_subset_Ioi_self
        · exact hFnorm_full.mono_set (Ioi_subset_Ioi zero_le_one)
      _ ≤ (9 / 95 : ℝ) := by linarith
  rw [completedRiemannZeta₀_eq_thetaMellin, norm_div, Complex.norm_two]
  linarith

theorem zeroBudget_norm_mul_sub_one_le_305_16 {s : ℂ}
    (hs0 : 0 ≤ s.re) (hs1 : s.re ≤ 1) (ht : |s.im| ≤ 17 / 4) :
    ‖s * (s - 1)‖ ≤ (305 / 16 : ℝ) := by
  have him : s.im ^ 2 ≤ (289 / 16 : ℝ) := by
    have h := mul_self_le_mul_self (abs_nonneg s.im) ht
    nlinarith [sq_abs s.im]
  have hre : s.re ^ 2 ≤ 1 := by nlinarith
  have hre' : (s.re - 1) ^ 2 ≤ 1 := by nlinarith
  have hn : ‖s‖ ^ 2 ≤ (305 / 16 : ℝ) := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    nlinarith
  have hn' : ‖s - 1‖ ^ 2 ≤ (305 / 16 : ℝ) := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im,
      Complex.one_im, sub_zero]
    nlinarith
  rw [norm_mul]
  nlinarith [sq_nonneg (‖s‖ - ‖s - 1‖)]

theorem zeroBudget_xi_ne_zero_of_abs_im_le_17_4 {s : ℂ}
    (hs0 : 0 ≤ s.re) (hs1 : s.re ≤ 1) (ht : |s.im| ≤ 17 / 4) :
    AWPIRH.xi s ≠ 0 := by
  intro hz
  have hraw : 1 + s * (s - 1) * completedRiemannZeta₀ s = 0 := by
    simpa [AWPIRH.xi] using hz
  have heq : s * (s - 1) * completedRiemannZeta₀ s = -1 := by
    linear_combination hraw
  have hnorm : ‖s * (s - 1) * completedRiemannZeta₀ s‖ = 1 := by
    rw [heq, norm_neg, norm_one]
  have hbound : ‖s * (s - 1) * completedRiemannZeta₀ s‖ ≤ (549 / 608 : ℝ) := by
    rw [norm_mul]
    calc
      ‖s * (s - 1)‖ * ‖completedRiemannZeta₀ s‖ ≤
          (305 / 16 : ℝ) * (9 / 190 : ℝ) :=
        mul_le_mul (zeroBudget_norm_mul_sub_one_le_305_16 hs0 hs1 ht)
          (zeroBudget_completedZeta0_norm_le_nine_190 hs0 hs1)
          (norm_nonneg _) (by norm_num)
      _ = _ := by norm_num
  linarith

theorem zeroBudget_xi_zero_17_4_lt_abs_im {s : ℂ} (hz : AWPIRH.xi s = 0) :
    (17 / 4 : ℝ) < |s.im| := by
  have hs := xi_zero_mem_critical_strip hz
  by_contra hn
  exact zeroBudget_xi_ne_zero_of_abs_im_le_17_4
    hs.1.le hs.2.le (le_of_not_gt hn) hz

theorem zeroBudget_theta_zero_angle_le_neg_285_293 {z : ℂ}
    (hz0 : z ≠ 0) (hz : AWPIRH.theta z = 0) :
    z.re / ‖z‖ ≤ -(285 / 293 : ℝ) := by
  let w := Complex.sqrt z
  have hsq : w ^ 2 = z := AWPIRH.complex_sqrt_sq z
  have hw : w ≠ 0 := by
    intro h
    apply hz0
    rw [← hsq, h]
    simp
  have hxi : AWPIRH.xi ((1 / 2 : ℂ) + w) = 0 := hz
  have hstrip := xi_zero_mem_critical_strip hxi
  have hbig := zeroBudget_xi_zero_17_4_lt_abs_im hxi
  have hwre : |w.re| < (1 / 2 : ℝ) := by
    apply abs_lt.mpr
    norm_num [Complex.add_re] at hstrip
    constructor <;> linarith
  have hwim : (17 / 4 : ℝ) < |w.im| := by simpa using hbig
  have hangle := square_angle_le_cutoff_of_le_abs_im
    (by norm_num : (0 : ℝ) < 17 / 2) hw
    (by nlinarith : (17 / 2 : ℝ) * |w.re| ≤ |w.im|)
  norm_num [hsq, slopeCutoff] at hangle
  exact hangle

theorem zeroBudget_actualComplexScale_four_abs_im_le_re (i : ActualPairIndex) :
    4 * |(actualComplexScale i).im| ≤ (actualComplexScale i).re := by
  have hn : 0 < ‖actualComplexScale i‖ :=
    norm_pos_iff.mpr (actualComplexScale_ne_zero i)
  have hangle := zeroBudget_theta_zero_angle_le_neg_285_293
    (neg_ne_zero.mpr (actualComplexScale_ne_zero i))
    (actual_theta_neg_complexScale_zero i)
  simp only [Complex.neg_re, norm_neg] at hangle
  have hre : (285 / 293 : ℝ) * ‖actualComplexScale i‖ ≤
      (actualComplexScale i).re := by
    have h := (div_le_iff₀ hn).mp hangle
    linarith
  have hrpos : 0 < (actualComplexScale i).re := by nlinarith
  have hsq := mul_self_le_mul_self
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 285 / 293) hn.le) hre
  have hnorm : (actualComplexScale i).re ^ 2 +
      (actualComplexScale i).im ^ 2 = ‖actualComplexScale i‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  by_contra hnot
  have hlt : (actualComplexScale i).re < 4 * |(actualComplexScale i).im| :=
    lt_of_not_ge hnot
  have hbad := mul_self_le_mul_self hrpos.le hlt.le
  nlinarith [sq_abs (actualComplexScale i).im, sq_pos_of_pos hn]

/-- The independent finite-height estimate gives the canonical four-wedge. -/
theorem zeroBudget_canonicalNode_four_abs_im_le_re (i : ActualPairIndex) :
    4 * |(canonicalNode i).im| ≤ (canonicalNode i).re := by
  have hd : 0 < Complex.normSq (actualComplexScale i) :=
    Complex.normSq_pos.mpr (actualComplexScale_ne_zero i)
  have hinv : 4 * |((actualComplexScale i)⁻¹).im| ≤
      ((actualComplexScale i)⁻¹).re := by
    rw [Complex.inv_im, Complex.inv_re, abs_div, abs_neg, abs_of_pos hd,
      ← mul_div_assoc]
    have h := mul_le_mul_of_nonneg_right
      (zeroBudget_actualComplexScale_four_abs_im_le_re i) (inv_pos.mpr hd).le
    simpa only [div_eq_mul_inv] using h
  rw [canonicalNode_eq_inverseScale_mul]
  simp only [← Complex.ofReal_inv, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero, zero_add, add_zero]
  rw [abs_mul, abs_of_pos (inv_pos.mpr actualKappa_pos)]
  nlinarith [mul_le_mul_of_nonneg_left hinv (inv_pos.mpr actualKappa_pos).le]

end RH_HilbertLimit
