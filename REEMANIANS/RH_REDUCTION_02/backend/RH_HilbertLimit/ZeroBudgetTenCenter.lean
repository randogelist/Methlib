import RH_HilbertLimit.ZeroBudgetFiveSector

/-!
# A central completed-zeta estimate for the next five cancellation checks

At the central argument, the two Mellin integrals have matching rational
bounds. This sharpens the strip estimate without changing its zero-free height.
Prepared by source inspection only; native compilation and audit are pending.
-/

set_option autoImplicit false
noncomputable section

namespace RH_HilbertLimit

open AngularMaster OverflowResidueRH MeasureTheory Set

/-- At the central argument the cubic theta envelope gives the bound 8/209. -/
theorem zeroBudget_completedZeta0_half_norm_le_eight_209 :
    ‖completedRiemannZeta₀ (1 / 2 : ℂ)‖ ≤ (8 / 209 : ℝ) := by
  let F : ℝ → ℂ := fun x =>
    (x : ℂ) ^ ((1 / 2 : ℂ) / 2 - 1) • hurwitzThetaMellinKernel x
  have hF_int : IntegrableOn F (Ioi 0) volume := by
    simpa only [F, MellinConvergent] using
      hurwitzThetaMellinKernel_convergent ((1 / 2 : ℂ) / 2)
  have hFnorm_full : IntegrableOn (fun x : ℝ => ‖F x‖) (Ioi 0) volume :=
    hF_int.norm
  have hFnorm (x : ℝ) (hx : 0 < x) :
      ‖F x‖ = x ^ (-(3 / 4) : ℝ) * ‖hurwitzThetaMellinKernel x‖ := by
    dsimp [F]
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
    norm_num
  have hupper_int : (∫ x : ℝ in Ioi 1, ‖F x‖) ≤ (8 / 209 : ℝ) := by
    have hmajor : IntegrableOn
        (fun x : ℝ => (2 / 19 : ℝ) * x ^ (-(15 / 4) : ℝ)) (Ioi 1) volume :=
      (integrableOn_Ioi_rpow_of_lt
        (by norm_num : (-(15 / 4) : ℝ) < -1)
        (by norm_num : (0 : ℝ) < 1)).const_mul _
    calc
      (∫ x : ℝ in Ioi 1, ‖F x‖) ≤
          ∫ x : ℝ in Ioi 1, (2 / 19 : ℝ) * x ^ (-(15 / 4) : ℝ) := by
        apply setIntegral_mono_on
          (hFnorm_full.mono_set (Ioi_subset_Ioi zero_le_one)) hmajor measurableSet_Ioi
        intro x hx
        have hxpos : 0 < x := zero_lt_one.trans hx
        rw [hFnorm x hxpos]
        calc
          x ^ (-(3 / 4) : ℝ) * ‖hurwitzThetaMellinKernel x‖ ≤
              x ^ (-(3 / 4) : ℝ) * ((2 / 19 : ℝ) * x ^ (-3 : ℝ)) :=
            mul_le_mul_of_nonneg_left (zeroBudget_thetaKernel_le_inverse_cube x hx.le)
              (Real.rpow_nonneg hxpos.le _)
          _ = (2 / 19 : ℝ) * x ^ (-(15 / 4) : ℝ) := by
            rw [mul_left_comm, ← Real.rpow_add hxpos]
            norm_num
      _ = (8 / 209 : ℝ) := by
        rw [integral_const_mul,
          integral_Ioi_rpow_of_lt (by norm_num : (-(15 / 4) : ℝ) < -1)
            (by norm_num : (0 : ℝ) < 1)]
        norm_num
  have hlower_int : (∫ x : ℝ in Ioc 0 1, ‖F x‖) ≤ (8 / 209 : ℝ) := by
    have hpow_interval :
        IntervalIntegrable (fun x : ℝ => x ^ (7 / 4 : ℝ)) volume 0 1 :=
      intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1 : ℝ) < 7 / 4)
    have hpow : IntegrableOn (fun x : ℝ => x ^ (7 / 4 : ℝ)) (Ioc 0 1) volume :=
      hpow_interval.1
    have hmajor : IntegrableOn
        (fun x : ℝ => (2 / 19 : ℝ) * x ^ (7 / 4 : ℝ)) (Ioc 0 1) volume :=
      hpow.const_mul (2 / 19 : ℝ)
    calc
      (∫ x : ℝ in Ioc 0 1, ‖F x‖) ≤
          ∫ x : ℝ in Ioc 0 1, (2 / 19 : ℝ) * x ^ (7 / 4 : ℝ) := by
        apply setIntegral_mono_on
          (hFnorm_full.mono_set Ioc_subset_Ioi_self) hmajor measurableSet_Ioc
        intro x hx
        rw [hFnorm x hx.1]
        calc
          x ^ (-(3 / 4) : ℝ) * ‖hurwitzThetaMellinKernel x‖ ≤
              x ^ (-(3 / 4) : ℝ) * ((2 / 19 : ℝ) * x ^ (5 / 2 : ℝ)) :=
            mul_le_mul_of_nonneg_left
              (zeroBudget_thetaKernel_le_five_halves x hx.1 hx.2)
              (Real.rpow_nonneg hx.1.le _)
          _ = (2 / 19 : ℝ) * x ^ (7 / 4 : ℝ) := by
            rw [mul_left_comm, ← Real.rpow_add hx.1]
            norm_num
      _ = (8 / 209 : ℝ) := by
        rw [integral_const_mul, ← intervalIntegral.integral_of_le zero_le_one,
          integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < 7 / 4))]
        norm_num
  have hbound :
      ‖mellin hurwitzThetaMellinKernel ((1 / 2 : ℂ) / 2)‖ ≤ (16 / 209 : ℝ) := by
    calc
      ‖mellin hurwitzThetaMellinKernel ((1 / 2 : ℂ) / 2)‖ =
          ‖∫ x : ℝ in Ioi 0, F x‖ := rfl
      _ ≤ ∫ x : ℝ in Ioi 0, ‖F x‖ := norm_integral_le_integral_norm _
      _ = (∫ x : ℝ in Ioc 0 1, ‖F x‖) + ∫ x : ℝ in Ioi 1, ‖F x‖ := by
        rw [← Ioc_union_Ioi_eq_Ioi zero_le_one,
          setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi]
        · exact hFnorm_full.mono_set Ioc_subset_Ioi_self
        · exact hFnorm_full.mono_set (Ioi_subset_Ioi zero_le_one)
      _ ≤ (16 / 209 : ℝ) := by linarith
  rw [completedRiemannZeta₀_eq_thetaMellin, norm_div, Complex.norm_two]
  linarith

end RH_HilbertLimit
