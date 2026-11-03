import HVR_PowerCorrection_Holomorphic

noncomputable section

/-!
Candidate unconditional denominator and termwise holomorphicity facts for the
complex correction. This does not establish a uniform majorant or identify
this correction with the von Mangoldt L-series. No Lean run was performed.
-/
namespace HVRCorrectionTermHolomorphic

open HVRPrimePowerCorrection HVRPowerCorrectionHolomorphic

/-- The norm of the complex prime ratio is the real ratio at the real part. -/
theorem complexRatio_norm (n : ℕ) (z : ℂ) :
    ‖complexRatio n z‖ = ratio z.re n := by
  simp only [complexRatio, ratio, Complex.norm_exp, Complex.mul_re,
    Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

/-- On Re(z)>a>1/2, every prime denominator is nonzero. -/
theorem complex_denominator_ne_zero (a : ℝ) (ha : (1 / 2 : ℝ) < a)
    {n : ℕ} (hp : Nat.Prime n) (z : ℂ) (hz : z ∈ halfPlane a) :
    (1 : ℂ) - complexRatio n z ≠ 0 := by
  have hzre : (1 / 2 : ℝ) < z.re := by
    have : a < z.re := hz
    linarith
  have hsmall : ‖complexRatio n z‖ < 1 := by
    rw [complexRatio_norm]
    have hle := ratio_le_two z.re hzre hp
    have hpos := denominator_uniform_pos z.re hzre
    linarith
  intro hzero
  have hone : complexRatio n z = 1 := (sub_eq_zero.mp hzero).symm
  rw [hone] at hsmall
  norm_num at hsmall

/-- Every summand is holomorphic on the strict half-plane. -/
theorem complexCorrectionTerm_differentiableOn
    (a : ℝ) (ha : (1 / 2 : ℝ) < a) (n : ℕ) :
    DifferentiableOn ℂ (complexCorrectionTerm n) (halfPlane a) := by
  by_cases hp : Nat.Prime n
  · have hnum : Differentiable ℂ (fun z : ℂ =>
        (Real.log (n : ℝ) : ℂ) * (complexRatio n z) ^ 2) := by
      unfold complexRatio
      fun_prop
    have hden : Differentiable ℂ (fun z : ℂ => 1 - complexRatio n z) := by
      unfold complexRatio
      fun_prop
    have hfun : complexCorrectionTerm n = (fun z : ℂ =>
        (Real.log (n : ℝ) : ℂ) * (complexRatio n z) ^ 2 /
          (1 - complexRatio n z)) := by
      funext z
      simp only [complexCorrectionTerm, if_pos hp]
    rw [hfun]
    exact hnum.differentiableOn.fun_div hden.differentiableOn
      (fun z hz => complex_denominator_ne_zero a ha hp z hz)
  · have hfun : complexCorrectionTerm n = (fun _ : ℂ => 0) := by
      funext z
      simp only [complexCorrectionTerm, if_neg hp]
    rw [hfun]
    fun_prop

/-- Once the explicit uniform norm bound is supplied, the previously
certified real correction series yields differentiability of the sum. -/
theorem complexCorrection_differentiableOn_of_uniform_bound
    (a : ℝ) (ha : (1 / 2 : ℝ) < a)
    (hbound : ∀ n z, z ∈ halfPlane a →
      ‖complexCorrectionTerm n z‖ ≤ correctionTerm a n) :
    DifferentiableOn ℂ complexCorrection (halfPlane a) := by
  apply complexCorrection_differentiableOn_of_bounds a ha
  · intro n
    exact complexCorrectionTerm_differentiableOn a ha n
  · exact hbound

end HVRCorrectionTermHolomorphic
