import HVR_Correction_TermHolomorphic

noncomputable section

/-!
Candidate proof of the concrete uniform majorant for the actual complex
prime-power correction. This is independent of any identity with zeta and
does not establish PNT. External Lean build and audit are required.
-/
namespace HVRCorrectionUniformBound

open HVRPrimeGram HVRPrimeSummability HVRPrimePowerCorrection
open HVRPowerCorrectionHolomorphic HVRCorrectionTermHolomorphic

theorem ratio_antitone_re {a b : ℝ} (hab : a ≤ b) {n : ℕ}
    (hp : Nat.Prime n) : ratio b n ≤ ratio a n := by
  have hn : (1 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (show 1 ≤ n from Nat.le_trans (by decide) hp.two_le)
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn
  have hprod : 0 ≤ (b - a) * Real.log (n : ℝ) :=
    mul_nonneg (sub_nonneg.mpr hab) hlog
  dsimp only [ratio]
  apply Real.exp_le_exp.mpr
  nlinarith

theorem ratio_sq_eq_weight_exp (a : ℝ) (n : ℕ) :
    ratio a n ^ 2 = Real.exp (-(2 * a) * Real.log (n : ℝ)) := by
  dsimp only [ratio]
  rw [pow_two, ← Real.exp_add]
  congr 1
  ring

/-- Uniform domination by the previously audited real correction series. -/
theorem complexCorrectionTerm_uniform_bound
    (a : ℝ) (ha : (1 / 2 : ℝ) < a)
    (n : ℕ) (z : ℂ) (hz : z ∈ halfPlane a) :
    ‖complexCorrectionTerm n z‖ ≤ correctionTerm a n := by
  by_cases hp : Nat.Prime n
  · have hzre : a ≤ z.re := le_of_lt hz
    have hn : (1 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast (show 1 ≤ n from Nat.le_trans (by decide) hp.two_le)
    have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn
    have hr0 : 0 ≤ ratio a n := le_of_lt (Real.exp_pos _)
    have hrz : 0 ≤ ratio z.re n := le_of_lt (Real.exp_pos _)
    have hratio : ratio z.re n ≤ ratio a n := ratio_antitone_re hzre hp
    have hsq : ratio z.re n ^ 2 ≤ ratio a n ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hratio) (add_nonneg hr0 hrz)]
    have hdenpos : 0 < 1 - ratio a n := by
      have hle := ratio_le_two a ha hp
      have hpos := denominator_uniform_pos a ha
      linarith
    have hden : 1 - ratio a n ≤ ‖(1 : ℂ) - complexRatio n z‖ := by
      have ht := norm_le_norm_sub_add (1 : ℂ) (complexRatio n z)
      simp only [norm_one, complexRatio_norm] at ht
      linarith
    have hnum : Real.log (n : ℝ) * ratio z.re n ^ 2 ≤
        Real.log (n : ℝ) * ratio a n ^ 2 :=
      mul_le_mul_of_nonneg_left hsq hlog
    have hfrac : (Real.log (n : ℝ) * ratio z.re n ^ 2) /
          ‖(1 : ℂ) - complexRatio n z‖ ≤
        (Real.log (n : ℝ) * ratio a n ^ 2) / (1 - ratio a n) :=
      div_le_div₀ (mul_nonneg hlog (sq_nonneg (ratio a n))) hnum hdenpos hden
    simpa only [complexCorrectionTerm, correctionTerm, primeWeightSeries,
      primeWeight, hp, if_true, Complex.norm_div, Complex.norm_mul,
      Complex.norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog,
      complexRatio_norm, ratio_sq_eq_weight_exp] using hfrac
  · simp [complexCorrectionTerm, correctionTerm, hp]

/-- The complex correction is holomorphic on every strict half-plane Re z>a>1/2. -/
theorem complexCorrection_differentiableOn
    (a : ℝ) (ha : (1 / 2 : ℝ) < a) :
    DifferentiableOn ℂ complexCorrection (halfPlane a) := by
  apply complexCorrection_differentiableOn_of_uniform_bound a ha
  intro n z hz
  exact complexCorrectionTerm_uniform_bound a ha n z hz

theorem complexCorrection_summable
    (a : ℝ) (ha : (1 / 2 : ℝ) < a) (z : ℂ) (hz : z ∈ halfPlane a) :
    Summable (fun n => complexCorrectionTerm n z) := by
  apply complexCorrection_summable_of_bound a ha z
  intro n
  exact complexCorrectionTerm_uniform_bound a ha n z hz

end HVRCorrectionUniformBound
