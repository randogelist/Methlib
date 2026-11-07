import RH_HilbertLimit.ZeroBudgetFirstMoment
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# A stronger independent sector for the second cancellation row

The concrete theta estimate is converted to a rational inverse-square
envelope. Retaining the split at one gives a completed-zeta bound of 1/6,
which excludes zeros up to height two. Consequently canonical cubes have
positive real part. This is finite-order progress, not an all-order claim.
Prepared by source inspection only; native compilation and audit are pending.
-/

set_option autoImplicit false
noncomputable section

namespace RH_HilbertLimit

open AngularMaster OverflowResidueRH MeasureTheory Set

private theorem zeroBudget_exp_three_mul_lower (x : ℝ) (hx : 1 ≤ x) :
    16 * x ^ 2 ≤ Real.exp (3 * x) := by
  have he : (8 / 3 : ℝ) ≤ Real.exp 1 := by
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1) 4
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    exact h
  have hxexp : x ≤ Real.exp (x - 1) := by
    have h := Real.add_one_le_exp (x - 1)
    linarith
  have hex : (8 / 3 : ℝ) * x ≤ Real.exp x := by
    calc
      (8 / 3 : ℝ) * x ≤ Real.exp 1 * Real.exp (x - 1) :=
        mul_le_mul he hxexp (by linarith) (Real.exp_nonneg _)
      _ = Real.exp x := by rw [← Real.exp_add]; congr 1 <;> ring
  have hc := pow_le_pow_left₀ (by positivity : 0 ≤ (8 / 3 : ℝ) * x) hex 3
  have hid : Real.exp (3 * x) = Real.exp x ^ 3 := by
    rw [show 3 * x = x + x + x by ring, Real.exp_add, Real.exp_add]
    ring
  rw [hid]
  have hpoly : x ^ 2 ≤ x ^ 3 := by
    nlinarith [mul_nonneg (sq_nonneg x) (sub_nonneg.mpr hx)]
  nlinarith [sq_nonneg x]

/-- A rational upper-tail envelope for the literal modified theta kernel. -/
theorem zeroBudget_thetaKernel_le_inverse_square (x : ℝ) (hx : 1 ≤ x) :
    ‖hurwitzThetaMellinKernel x‖ ≤ (1 / 6 : ℝ) * x ^ (-2 : ℝ) := by
  have hxpos : 0 < x := by linarith
  have hpi : (3 : ℝ) ≤ Real.pi := Real.pi_gt_three.le
  have hpx : (3 : ℝ) ≤ Real.pi * x := by nlinarith
  have hfour : (4 : ℝ) ≤ Real.exp 3 := by
    have h := Real.add_one_le_exp (3 : ℝ)
    linarith
  have hE : Real.exp (-Real.pi * x) ≤ (1 / 4 : ℝ) := by
    have hnegthree : Real.exp (-3) ≤ (1 / 4 : ℝ) := by
      rw [Real.exp_neg, inv_eq_one_div]
      exact (div_le_iff₀ (Real.exp_pos 3)).2 (by linarith)
    exact (Real.exp_le_exp.mpr (by nlinarith : -Real.pi * x ≤ -3)).trans hnegthree
  have hden : 0 < 1 - Real.exp (-Real.pi * x) := by linarith
  have hfrac : 2 / (1 - Real.exp (-Real.pi * x)) ≤ (8 / 3 : ℝ) := by
    apply (div_le_iff₀ hden).2
    linarith
  have hsmall : Real.exp (-Real.pi * x) ≤ 1 / (16 * x ^ 2) := by
    calc
      Real.exp (-Real.pi * x) ≤ Real.exp (-(3 * x)) := by
        apply Real.exp_le_exp.mpr
        nlinarith
      _ = 1 / Real.exp (3 * x) := by rw [Real.exp_neg, inv_eq_one_div]
      _ ≤ 1 / (16 * x ^ 2) :=
        one_div_le_one_div_of_le (by positivity)
          (zeroBudget_exp_three_mul_lower x hx)
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
    _ ≤ (8 / 3 : ℝ) * Real.exp (-Real.pi * x) :=
      mul_le_mul_of_nonneg_right hfrac (Real.exp_nonneg _)
    _ ≤ (8 / 3 : ℝ) * (1 / (16 * x ^ 2)) :=
      mul_le_mul_of_nonneg_left hsmall (by norm_num)
    _ = (1 / 6 : ℝ) * x ^ (-2 : ℝ) := by
      rw [Real.rpow_neg hxpos.le]
      norm_num <;> field_simp [hxpos.ne'] <;> ring

/-- The same envelope below one, using exact theta inversion. -/
theorem zeroBudget_thetaKernel_le_three_halves (x : ℝ)
    (hx : 0 < x) (hxone : x ≤ 1) :
    ‖hurwitzThetaMellinKernel x‖ ≤ (1 / 6 : ℝ) * x ^ (3 / 2 : ℝ) := by
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
        (1 / x) ^ (1 / 2 : ℝ) * ((1 / 6 : ℝ) * (1 / x) ^ (-2 : ℝ)) :=
      mul_le_mul_of_nonneg_left (zeroBudget_thetaKernel_le_inverse_square (1 / x) hyone)
        (Real.rpow_nonneg hypos.le _)
    _ = (1 / 6 : ℝ) * (1 / x) ^ (-(3 / 2 : ℝ)) := by
      rw [mul_left_comm, ← Real.rpow_add hypos]
      norm_num
    _ = (1 / 6 : ℝ) * x ^ (3 / 2 : ℝ) := by
      rw [one_div x, Real.inv_rpow hx.le, ← Real.rpow_neg hx.le, neg_neg]

/-- Keeping the actual two integration domains improves the strip bound. -/
theorem zeroBudget_completedZeta0_norm_le_one_sixth {s : ℂ}
    (hs0 : 0 ≤ s.re) (hs1 : s.re ≤ 1) :
    ‖completedRiemannZeta₀ s‖ ≤ (1 / 6 : ℝ) := by
  let F : ℝ → ℂ := fun x => (x : ℂ) ^ (s / 2 - 1) • hurwitzThetaMellinKernel x
  have hF_int : IntegrableOn F (Ioi 0) := by
    simpa only [F, MellinConvergent] using hurwitzThetaMellinKernel_convergent (s / 2)
  have hFnorm_full : IntegrableOn (fun x : ℝ => ‖F x‖) (Ioi 0) := hF_int.norm
  have hFnorm (x : ℝ) (hx : 0 < x) :
      ‖F x‖ = x ^ (s.re / 2 - 1) * ‖hurwitzThetaMellinKernel x‖ := by
    dsimp [F]
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
    simp
  have hupper_int : (∫ x : ℝ in Ioi 1, ‖F x‖) ≤ (1 / 6 : ℝ) := by
    have hmajor : IntegrableOn (fun x : ℝ => (1 / 6 : ℝ) * x ^ (-2 : ℝ)) (Ioi 1) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1)
        (by norm_num : (0 : ℝ) < 1)).const_mul _
    calc
      (∫ x : ℝ in Ioi 1, ‖F x‖) ≤
          ∫ x : ℝ in Ioi 1, (1 / 6 : ℝ) * x ^ (-2 : ℝ) := by
        apply setIntegral_mono_on
          (hFnorm_full.mono_set (Ioi_subset_Ioi zero_le_one)) hmajor measurableSet_Ioi
        intro x hx
        rw [hFnorm x (zero_lt_one.trans hx)]
        have hpow : x ^ (s.re / 2 - 1) ≤ 1 := by
          calc
            x ^ (s.re / 2 - 1) ≤ x ^ (0 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hx.le (by linarith)
            _ = 1 := by simp
        calc
          x ^ (s.re / 2 - 1) * ‖hurwitzThetaMellinKernel x‖ ≤
              1 * ‖hurwitzThetaMellinKernel x‖ :=
            mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
          _ ≤ _ := by simpa using zeroBudget_thetaKernel_le_inverse_square x hx.le
      _ = (1 / 6 : ℝ) := by
        rw [integral_const_mul,
          integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1)
            (by norm_num : (0 : ℝ) < 1)]
        norm_num
  have hlower_int : (∫ x : ℝ in Ioc 0 1, ‖F x‖) ≤ (1 / 6 : ℝ) := by
    have hmajor : IntegrableOn (fun _x : ℝ => (1 / 6 : ℝ)) (Ioc 0 1) := by
      simp [integrableOn_const]
    calc
      (∫ x : ℝ in Ioc 0 1, ‖F x‖) ≤
          ∫ _x : ℝ in Ioc 0 1, (1 / 6 : ℝ) := by
        apply setIntegral_mono_on
          (hFnorm_full.mono_set Ioc_subset_Ioi_self) hmajor measurableSet_Ioc
        intro x hx
        rw [hFnorm x hx.1]
        have hpow : x ^ (s.re / 2 + 1 / 2) ≤ 1 := by
          calc
            x ^ (s.re / 2 + 1 / 2) ≤ x ^ (0 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_ge hx.1 hx.2 (by linarith)
            _ = 1 := by simp
        calc
          x ^ (s.re / 2 - 1) * ‖hurwitzThetaMellinKernel x‖ ≤
              x ^ (s.re / 2 - 1) * ((1 / 6 : ℝ) * x ^ (3 / 2 : ℝ)) :=
            mul_le_mul_of_nonneg_left
              (zeroBudget_thetaKernel_le_three_halves x hx.1 hx.2)
              (Real.rpow_nonneg hx.1.le _)
          _ = (1 / 6 : ℝ) * x ^ (s.re / 2 + 1 / 2) := by
            rw [mul_left_comm, ← Real.rpow_add hx.1]
            congr 2 <;> ring
          _ ≤ (1 / 6 : ℝ) := by nlinarith
      _ = (1 / 6 : ℝ) := by simp
  have hbound : ‖mellin hurwitzThetaMellinKernel (s / 2)‖ ≤ (1 / 3 : ℝ) := by
    calc
      ‖mellin hurwitzThetaMellinKernel (s / 2)‖ = ‖∫ x : ℝ in Ioi 0, F x‖ := rfl
      _ ≤ ∫ x : ℝ in Ioi 0, ‖F x‖ := norm_integral_le_integral_norm _
      _ = (∫ x : ℝ in Ioc 0 1, ‖F x‖) + ∫ x : ℝ in Ioi 1, ‖F x‖ := by
        rw [← Ioc_union_Ioi_eq_Ioi zero_le_one,
          setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi]
        · exact hFnorm_full.mono_set Ioc_subset_Ioi_self
        · exact hFnorm_full.mono_set (Ioi_subset_Ioi zero_le_one)
      _ ≤ (1 / 3 : ℝ) := by linarith
  rw [completedRiemannZeta₀_eq_thetaMellin, norm_div, Complex.norm_two]
  linarith

theorem zeroBudget_norm_mul_sub_one_le_five {s : ℂ}
    (hs0 : 0 ≤ s.re) (hs1 : s.re ≤ 1) (ht : |s.im| ≤ 2) :
    ‖s * (s - 1)‖ ≤ 5 := by
  have him : s.im ^ 2 ≤ 4 := by
    have h := mul_self_le_mul_self (abs_nonneg s.im) ht
    nlinarith [sq_abs s.im]
  have hre : s.re ^ 2 ≤ 1 := by nlinarith
  have hre' : (s.re - 1) ^ 2 ≤ 1 := by nlinarith
  have hn : ‖s‖ ^ 2 ≤ 5 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    nlinarith
  have hn' : ‖s - 1‖ ^ 2 ≤ 5 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im,
      Complex.one_im, sub_zero]
    nlinarith
  rw [norm_mul]
  nlinarith [sq_nonneg (‖s‖ - ‖s - 1‖)]

theorem zeroBudget_xi_ne_zero_of_abs_im_le_two {s : ℂ}
    (hs0 : 0 ≤ s.re) (hs1 : s.re ≤ 1) (ht : |s.im| ≤ 2) :
    AWPIRH.xi s ≠ 0 := by
  intro hz
  have hraw : 1 + s * (s - 1) * completedRiemannZeta₀ s = 0 := by
    simpa [AWPIRH.xi] using hz
  have heq : s * (s - 1) * completedRiemannZeta₀ s = -1 := by
    linear_combination hraw
  have hnorm : ‖s * (s - 1) * completedRiemannZeta₀ s‖ = 1 := by
    rw [heq, norm_neg, norm_one]
  have hbound : ‖s * (s - 1) * completedRiemannZeta₀ s‖ ≤ (5 / 6 : ℝ) := by
    rw [norm_mul]
    calc
      ‖s * (s - 1)‖ * ‖completedRiemannZeta₀ s‖ ≤ 5 * (1 / 6 : ℝ) :=
        mul_le_mul (zeroBudget_norm_mul_sub_one_le_five hs0 hs1 ht)
          (zeroBudget_completedZeta0_norm_le_one_sixth hs0 hs1)
          (norm_nonneg _) (by norm_num)
      _ = _ := by norm_num
  linarith

theorem zeroBudget_xi_zero_two_lt_abs_im {s : ℂ} (hz : AWPIRH.xi s = 0) :
    2 < |s.im| := by
  have hs := xi_zero_mem_critical_strip hz
  by_contra hn
  exact zeroBudget_xi_ne_zero_of_abs_im_le_two
    hs.1.le hs.2.le (le_of_not_gt hn) hz

theorem zeroBudget_theta_zero_angle_le_neg_15_17 {z : ℂ}
    (hz0 : z ≠ 0) (hz : AWPIRH.theta z = 0) :
    z.re / ‖z‖ ≤ -(15 / 17 : ℝ) := by
  let w := Complex.sqrt z
  have hsq : w ^ 2 = z := AWPIRH.complex_sqrt_sq z
  have hw : w ≠ 0 := by
    intro h
    apply hz0
    rw [← hsq, h]
    simp
  have hxi : AWPIRH.xi ((1 / 2 : ℂ) + w) = 0 := hz
  have hstrip := xi_zero_mem_critical_strip hxi
  have hbig := zeroBudget_xi_zero_two_lt_abs_im hxi
  have hwre : |w.re| < (1 / 2 : ℝ) := by
    apply abs_lt.mpr
    norm_num [Complex.add_re] at hstrip
    constructor <;> linarith
  have hwim : (2 : ℝ) < |w.im| := by simpa using hbig
  have hangle := square_angle_le_cutoff_of_le_abs_im
    (by norm_num : (0 : ℝ) < 4) hw
    (by nlinarith : (4 : ℝ) * |w.re| ≤ |w.im|)
  norm_num [hsq, slopeCutoff] at hangle
  exact hangle

theorem zeroBudget_actualComplexScale_cube_re_pos (i : ActualPairIndex) :
    0 < (actualComplexScale i ^ 3).re := by
  have hn : 0 < ‖actualComplexScale i‖ :=
    norm_pos_iff.mpr (actualComplexScale_ne_zero i)
  have hangle := zeroBudget_theta_zero_angle_le_neg_15_17
    (neg_ne_zero.mpr (actualComplexScale_ne_zero i))
    (actual_theta_neg_complexScale_zero i)
  simp only [Complex.neg_re, norm_neg] at hangle
  have hre : (15 / 17 : ℝ) * ‖actualComplexScale i‖ ≤
      (actualComplexScale i).re := by
    have h := (div_le_iff₀ hn).mp hangle
    linarith
  have hrpos : 0 < (actualComplexScale i).re := by nlinarith
  have hsq := mul_self_le_mul_self
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 15 / 17) hn.le) hre
  have hnorm : (actualComplexScale i).re ^ 2 +
      (actualComplexScale i).im ^ 2 = ‖actualComplexScale i‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  have hfactor : 0 < (actualComplexScale i).re ^ 2 -
      3 * (actualComplexScale i).im ^ 2 := by
    nlinarith [sq_pos_of_pos hn]
  have heq : (actualComplexScale i ^ 3).re =
      (actualComplexScale i).re * ((actualComplexScale i).re ^ 2 -
        3 * (actualComplexScale i).im ^ 2) := by
    simp only [pow_succ, pow_zero, one_mul, Complex.mul_re, Complex.mul_im]
    ring
  rw [heq]
  exact mul_pos hrpos hfactor

/-- The literal cubic canonical summands are strictly real-positive. -/
theorem zeroBudget_canonicalNode_cube_re_pos (i : ActualPairIndex) :
    0 < (canonicalNode i ^ 3).re := by
  have hinv : 0 < (((actualComplexScale i)⁻¹) ^ 3).re := by
    have heq : ((actualComplexScale i)⁻¹) ^ 3 =
        (actualComplexScale i ^ 3)⁻¹ := by simp only [inv_pow]
    rw [heq, Complex.inv_re]
    exact div_pos (zeroBudget_actualComplexScale_cube_re_pos i)
      (Complex.normSq_pos.mpr (pow_ne_zero 3 (actualComplexScale_ne_zero i)))
  rw [canonicalNode_eq_inverseScale_mul, mul_pow]
  simp only [← Complex.ofReal_inv, ← Complex.ofReal_pow,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact mul_pos (pow_pos (inv_pos.mpr actualKappa_pos) 3) hinv

end RH_HilbertLimit
