import ConcreteABCDUnifiedClosure

/-! The positive-frequency periodic shear on the unit torus. The geometric
    formula for the initial profile supplies its spatial analyticity. -/

noncomputable section

open Fefferman Fefferman.ConcreteReal

namespace CondFeffB

def shearMode (ν t y : ℝ) (k : ℕ) : ℝ :=
  Real.exp (-((k + 1 : ℕ) : ℝ)) *
    Real.exp (-(4 * Real.pi ^ 2 * ν * ((k + 1 : ℕ) : ℝ) ^ 2) * t) *
    Real.cos (2 * Real.pi * ((k + 1 : ℕ) : ℝ) * y)

def shearProfile (ν t y : ℝ) : ℝ := ∑' k : ℕ, shearMode ν t y k

def shearVelocity (ν : ℝ) : RVelocity := fun x t i =>
  if i = 0 then shearProfile ν t (x 1) else 0

theorem shearVelocity_first (ν : ℝ) (x : RSpace) (t : ℝ) :
    shearVelocity ν x t 0 = shearProfile ν t (x 1) := by simp [shearVelocity]

theorem shearMode_at_origin (ν t : ℝ) (k : ℕ) :
    shearMode ν t 0 k = Real.exp (-((k + 1 : ℕ) : ℝ)) *
      Real.exp (-(4 * Real.pi ^ 2 * ν * ((k + 1 : ℕ) : ℝ) ^ 2) * t) := by
  simp [shearMode]

theorem shearWeights_summable : Summable (fun k : ℕ => Real.exp (-((k + 1 : ℕ) : ℝ))) := by
  have hgeom := summable_geometric_of_lt_one (Real.exp_pos (-1)).le
    (Real.exp_lt_one_iff.mpr (by norm_num : (-1 : ℝ) < 0))
  have hshift : Summable (fun k : ℕ => Real.exp (-1) ^ (k + 1)) := by
    simpa only [pow_succ] using hgeom.mul_right (Real.exp (-1))
  apply hshift.congr
  intro k
  rw [← Real.exp_nat_mul]
  congr 1 <;> ring

theorem shearMode_norm_le (ν t y : ℝ) (hν : 0 ≤ ν) (ht : 0 ≤ t) (k : ℕ) :
    ‖shearMode ν t y k‖ ≤ Real.exp (-((k + 1 : ℕ) : ℝ)) := by
  have he : Real.exp (-(4 * Real.pi ^ 2 * ν * ((k + 1 : ℕ) : ℝ) ^ 2) * t) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    apply mul_nonpos_of_nonpos_of_nonneg _ ht
    exact neg_nonpos.mpr (by positivity)
  rw [Real.norm_eq_abs, shearMode, abs_mul, abs_mul,
    abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ (Real.exp (-((k + 1 : ℕ) : ℝ)) *
        Real.exp (-(4 * Real.pi ^ 2 * ν * ((k + 1 : ℕ) : ℝ) ^ 2) * t)) * 1 :=
      mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (by positivity)
    _ ≤ _ := by
      rw [mul_one]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left he
        (Real.exp_pos (-((k + 1 : ℕ) : ℝ))).le

theorem shearMode_summable (ν t y : ℝ) (hν : 0 ≤ ν) (ht : 0 ≤ t) :
    Summable (shearMode ν t y) :=
  shearWeights_summable.of_norm_bounded (shearMode_norm_le ν t y hν ht)

theorem shearProfile_continuousOn (ν : ℝ) (hν : 0 ≤ ν) :
    ContinuousOn (fun p : ℝ × ℝ => shearProfile ν p.1 p.2) {p : ℝ × ℝ | 0 ≤ p.1} := by
  unfold shearProfile
  apply continuousOn_tsum (u := fun k : ℕ => Real.exp (-((k + 1 : ℕ) : ℝ)))
  · intro k
    apply Continuous.continuousOn
    unfold shearMode
    fun_prop
  · exact shearWeights_summable
  · exact fun k p hp => shearMode_norm_le ν p.1 p.2 hν hp k

theorem shearVelocity_continuousOn (ν : ℝ) (hν : 0 ≤ ν) (i : Fin 3) :
    ContinuousOn (fun p : RSpace × ℝ => shearVelocity ν p.1 p.2 i)
      {p : RSpace × ℝ | 0 ≤ p.2} := by
  by_cases hi : i = 0
  · simp only [shearVelocity, if_pos hi]
    have hmap : Continuous (fun p : RSpace × ℝ => (p.2, p.1 1)) := by fun_prop
    exact (shearProfile_continuousOn ν hν).comp hmap.continuousOn (fun _ hp => hp)
  · simp only [shearVelocity, if_neg hi]
    exact continuousOn_const

theorem shearMode_period_one (ν t y : ℝ) (k : ℕ) :
    shearMode ν t (y + 1) k = shearMode ν t y k := by
  unfold shearMode
  rw [show 2 * Real.pi * ((k + 1 : ℕ) : ℝ) * (y + 1) =
    2 * Real.pi * ((k + 1 : ℕ) : ℝ) * y + ((k + 1 : ℕ) : ℝ) * (2 * Real.pi) by ring,
    Real.cos_add_nat_mul_two_pi]

theorem shearProfile_period_one (ν t y : ℝ) :
    shearProfile ν t (y + 1) = shearProfile ν t y :=
  tsum_congr (shearMode_period_one ν t y)

theorem shearVelocity_periodic (ν : ℝ) : vectorPeriodic realAnalysis (shearVelocity ν) := by
  intro x t _ j
  funext i
  by_cases hj : (1 : Fin 3) = j
  · subst j
    simp [shearVelocity, unitShift, realAnalysis, shearProfile_period_one]
  · simp [shearVelocity, unitShift, realAnalysis, hj]

private def phase (y : ℝ) : ℂ :=
  -1 + Complex.ofRealCLM (2 * Real.pi * y) * Complex.I

private def ratio (y : ℝ) : ℂ := Complex.exp (phase y)

private theorem ratio_norm_lt (y : ℝ) : ‖ratio y‖ < 1 := by
  rw [ratio, Complex.norm_exp, Real.exp_lt_one_iff]
  norm_num [phase, Complex.mul_re]

private theorem ratio_den_ne (y : ℝ) : (1 : ℂ) - ratio y ≠ 0 := by
  intro h
  have he := (sub_eq_zero.mp h).symm
  have hlt := ratio_norm_lt y
  rw [he, norm_one] at hlt
  exact (lt_irrefl _) hlt

/-- Real part of the geometric sum q + q² + ..., with |q| = exp(-1). -/
def initialProfile (y : ℝ) : ℝ :=
  ((1 - ratio y)⁻¹ * ratio y).re

private theorem ratio_pow_re (y : ℝ) (n : ℕ) :
    (ratio y ^ n).re = Real.exp (-(n : ℝ)) * Real.cos (2 * Real.pi * (n : ℝ) * y) := by
  have hre : ((n : ℂ) * phase y).re = -(n : ℝ) := by simp [phase, Complex.mul_re] <;> ring
  have him : ((n : ℂ) * phase y).im = 2 * Real.pi * (n : ℝ) * y := by
    simp [phase, Complex.mul_im, Complex.mul_re] <;> ring
  rw [ratio, ← Complex.exp_nat_mul, Complex.exp_re, hre, him]

theorem shearProfile_initial (ν y : ℝ) : shearProfile ν 0 y = initialProfile y := by
  have hg : HasSum (fun k : ℕ => ratio y ^ (k + 1)) ((1 - ratio y)⁻¹ * ratio y) := by
    simpa only [pow_succ] using (hasSum_geometric_of_norm_lt_one (ratio_norm_lt y)).mul_right (ratio y)
  calc
    shearProfile ν 0 y = ∑' k : ℕ, (ratio y ^ (k + 1)).re := by
      unfold shearProfile
      apply tsum_congr
      intro k
      rw [ratio_pow_re]
      simp [shearMode]
    _ = initialProfile y := (Complex.hasSum_re hg).tsum_eq

theorem initialProfile_contDiff : ContDiff ℝ ⊤ initialProfile := by
  have harg : ContDiff ℝ ⊤ (fun y : ℝ => 2 * Real.pi * y) := by fun_prop
  have hz : ContDiff ℝ ⊤ phase :=
    contDiff_const.add ((Complex.ofRealCLM.contDiff.comp harg).mul contDiff_const)
  have hq : ContDiff ℝ ⊤ ratio := hz.cexp
  have hinv : ContDiff ℝ ⊤ (fun y => (1 - ratio y)⁻¹) :=
    (contDiff_const.sub hq).inv ratio_den_ne
  exact Complex.reCLM.contDiff.comp (hinv.mul hq)

def shearDatum : RInitial := fun x i =>
  if i = 0 then initialProfile (x 1) else 0

theorem shearVelocity_initial (ν : ℝ) (x : RSpace) : shearVelocity ν x 0 = shearDatum x := by
  funext i
  simp only [shearVelocity, shearDatum, shearProfile_initial]

theorem shearDatum_periodic : initialPeriodic realAnalysis shearDatum := by
  intro x j
  rw [← shearVelocity_initial 1 (unitShift realAnalysis x j), ← shearVelocity_initial 1 x]
  exact shearVelocity_periodic 1 x 0 (by change (0 : ℝ) ≤ 0; exact le_rfl) j

theorem shearDatum_smooth : initialSmooth realAnalysis shearDatum := by
  intro i
  by_cases h : i = 0
  · simp only [shearDatum, if_pos h]
    exact initialProfile_contDiff.comp (contDiff_apply ℝ ℝ (1 : Fin 3))
  · simp only [shearDatum, if_neg h]
    exact contDiff_const

theorem shearDatum_divergenceFree : initialDivergenceFree realAnalysis shearDatum := by
  intro x
  have hp := hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 3) x
  have hf := (initialProfile_contDiff.differentiable (by simp) (x 1)).hasFDerivAt
  have hfirst : spatialDerivative 0 (fun y : RSpace => initialProfile (y 1)) x = 0 := by
    change fderiv ℝ (initialProfile ∘ fun y : RSpace => y 1) x (basisDirection 0) = 0
    rw [(hf.comp x hp).fderiv]
    simp [ContinuousLinearMap.comp_apply, basisDirection]
  change spatialDerivative 0 (fun y => shearDatum y 0) x +
    spatialDerivative 1 (fun y => shearDatum y 1) x +
    spatialDerivative 2 (fun y => shearDatum y 2) x = 0
  simpa [shearDatum, spatialDerivative, (by decide : (2 : Fin 3) ≠ 0)] using hfirst

theorem shearDatum_admissible : admissibleInitial realAnalysis .periodic shearDatum :=
  ⟨shearDatum_smooth, shearDatum_divergenceFree, shearDatum_periodic⟩

end CondFeffB
