import WJINewtonDifferentiate
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace CondFeffA
open Fefferman.ConcreteReal MeasureTheory Set Filter Metric
open scoped ContDiff Topology
noncomputable section

local notation "D" => spatialDerivative

private lemma q_nonneg (x : RSpace) : 0 ≤ normSq3 x := by
  unfold normSq3
  nlinarith only [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2)]

private lemma q_smooth : ContDiff ℝ ⊤ normSq3 := by unfold normSq3; fun_prop

private lemma q_partial (i : Fin 3) (x : RSpace) : D i normSq3 x = 2*x i := by
  have coord (j : Fin 3) : D i (fun y : RSpace => y j) x = basisDirection i j := by
    unfold spatialDerivative
    rw [(hasFDerivAt_apply (𝕜 := ℝ) j x).fderiv] <;> rfl
  have square (j : Fin 3) :
      D i (fun y : RSpace => y j * y j) x = x j * basisDirection i j + x j * basisDirection i j := by
    have h : DifferentiableAt ℝ (fun y : RSpace => y j) x := by fun_prop
    change (fderiv ℝ (fun y : RSpace => y j * y j) x) (basisDirection i) = _
    rw [fderiv_fun_mul h h]
    change x j * D i (fun y : RSpace => y j) x + x j * D i (fun y : RSpace => y j) x = _
    rw [coord j]
  change D i (fun y : RSpace => (y 0*y 0+y 1*y 1)+y 2*y 2) x = _
  rw [partial_add (f := fun y : RSpace => y 0*y 0+y 1*y 1)
      (g := fun y : RSpace => y 2*y 2) (by fun_prop) (by fun_prop),
    partial_add (f := fun y : RSpace => y 0*y 0) (g := fun y : RSpace => y 1*y 1)
      (by fun_prop) (by fun_prop), square 0, square 1, square 2]
  fin_cases i
  · change (x 0 * 1 + x 0 * 1) + (x 1 * 0 + x 1 * 0) + (x 2 * 0 + x 2 * 0) = 2*x 0
    ring
  · change (x 0 * 0 + x 0 * 0) + (x 1 * 1 + x 1 * 1) + (x 2 * 0 + x 2 * 0) = 2*x 1
    ring
  · change (x 0 * 0 + x 0 * 0) + (x 1 * 0 + x 1 * 0) + (x 2 * 1 + x 2 * 1) = 2*x 2
    ring

private def regularScalar (ε t : ℝ) : ℝ := (4*Real.pi * Real.sqrt (ε+t))⁻¹
private def regular (ε : ℝ) : RSpace → ℝ := regularScalar ε ∘ normSq3
private def regularGradient (ε : ℝ) (i : Fin 3) (x : RSpace) : ℝ :=
  -(x i) / (4*Real.pi * (Real.sqrt (ε + normSq3 x))^3)

private lemma radius_pos {ε : ℝ} (hε : 0 < ε) (x : RSpace) :
    0 < Real.sqrt (ε+normSq3 x) :=
  Real.sqrt_pos.mpr (add_pos_of_pos_of_nonneg hε (q_nonneg x))

private lemma reg_smooth {ε : ℝ} (hε : 0 < ε) : ContDiff ℝ ∞ (regular ε) := by
  have hs : ContDiff ℝ ∞ (fun x : RSpace => ε+normSq3 x) :=
    contDiff_const.add (q_smooth.of_le le_top)
  have hr := hs.sqrt (fun x => (add_pos_of_pos_of_nonneg hε (q_nonneg x)).ne')
  exact (contDiff_const.mul hr).inv (fun x =>
    mul_ne_zero (by positivity : (4*Real.pi : ℝ) ≠ 0) (radius_pos hε x).ne')

private lemma regular_partial_at (ε : ℝ) (i : Fin 3) (x : RSpace) (hε : 0 < ε+normSq3 x) :
    D i (regular ε) x = regularGradient ε i x := by
  let s := normSq3 x
  let r := Real.sqrt (ε+s)
  have hs : 0 < ε+s := hε
  have hr : 0 < r := Real.sqrt_pos.mpr hs
  have hC : 0 < 4*Real.pi := by positivity
  have hden : 4*Real.pi*r ≠ 0 := mul_ne_zero hC.ne' hr.ne'
  have hd : HasDerivAt (fun t : ℝ => ε+t) 1 s := by
    simpa using (hasDerivAt_id s).const_add ε
  have hfull : HasDerivAt (regularScalar ε)
      (-(4*Real.pi * (1 / (2*r))) / (4*Real.pi*r)^2) s :=
    ((hd.sqrt hs.ne').const_mul (4*Real.pi)).inv hden
  have hq := q_smooth.differentiable (by simp) x
  change (fderiv ℝ (regularScalar ε ∘ normSq3) x) (basisDirection i) = _
  rw [fderiv_comp x hfull.differentiableAt hq, ContinuousLinearMap.comp_apply,
    fderiv_eq_smul_deriv, smul_eq_mul]
  change D i normSq3 x * deriv (regularScalar ε) s = _
  rw [q_partial i x, hfull.deriv]
  change 2*x i * (-(4*Real.pi*(1/(2*r))) / (4*Real.pi*r)^2) = -(x i)/(4*Real.pi*r^3)
  field_simp [Real.pi_ne_zero, hr.ne'] <;> ring

private lemma regular_partial {ε : ℝ} (hε : 0 < ε) (i : Fin 3) (x : RSpace) :
    D i (regular ε) x = regularGradient ε i x :=
  regular_partial_at ε i x (add_pos_of_pos_of_nonneg hε (q_nonneg x))

/-- Classical coordinate derivative of the literal Newton kernel off its pole. -/
theorem wji_newtonKernel_partial_of_ne_zero (i : Fin 3) {x : RSpace} (hx : x ≠ 0) :
    D i newtonKernel x = newtonGradientKernel i x := by
  have hn : 0 < euclideanNorm3 x := (norm_pos_iff.mpr hx).trans_le (norm_le_newton_radius x)
  have hs : 0 < (0:ℝ)+normSq3 x := by
    rw [zero_add]
    exact Real.sqrt_pos.mp hn
  have hK : regular 0 = newtonKernel := by
    funext y
    simp only [regular, regularScalar, Function.comp_apply, zero_add, newtonKernel, euclideanNorm3]
  have h := regular_partial_at 0 i x hs
  rw [hK] at h
  simpa only [regularGradient, zero_add, newtonGradientKernel, euclideanNorm3] using h

private lemma reg_grad_cont {ε : ℝ} (hε : 0 < ε) (i : Fin 3) : Continuous (regularGradient ε i) := by
  unfold regularGradient
  apply Continuous.div
  · fun_prop
  · unfold normSq3
    fun_prop
  · intro x
    exact mul_ne_zero (by positivity) (pow_ne_zero _ (radius_pos hε x).ne')

private lemma reg_bounds {ε : ℝ} (hε : 0 < ε) (i : Fin 3) {y : RSpace} (hy : y ≠ 0) :
    ‖regular ε y‖ ≤ ‖newtonKernel y‖ ∧
    ‖regularGradient ε i y‖ ≤ ‖newtonGradientKernel i y‖ := by
  let a := euclideanNorm3 y
  let b := Real.sqrt (ε+normSq3 y)
  have ha : 0 < a := (norm_pos_iff.mpr hy).trans_le (norm_le_newton_radius y)
  have hb : 0 < b := radius_pos hε y
  have hab : a ≤ b := Real.sqrt_le_sqrt (by linarith only [hε] : normSq3 y ≤ ε+normSq3 y)
  have hC : 0 < 4*Real.pi := by positivity
  constructor
  · change ‖(4*Real.pi*b)⁻¹‖ ≤ ‖(4*Real.pi*a)⁻¹‖
    rw [Real.norm_of_nonneg (inv_nonneg.mpr (mul_nonneg hC.le hb.le)),
      Real.norm_of_nonneg (inv_nonneg.mpr (mul_nonneg hC.le ha.le))]
    exact inv_anti₀ (mul_pos hC ha) (mul_le_mul_of_nonneg_left hab hC.le)
  · change ‖-(y i)/(4*Real.pi*b^3)‖ ≤ ‖-(y i)/(4*Real.pi*a^3)‖
    rw [norm_div, norm_div, Real.norm_of_nonneg (mul_nonneg hC.le (pow_nonneg hb.le 3)),
      Real.norm_of_nonneg (mul_nonneg hC.le (pow_nonneg ha.le 3))]
    exact div_le_div_of_nonneg_left (norm_nonneg _) (mul_pos hC (pow_pos ha _))
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha.le hab 3) hC.le)

private def eps (n : ℕ) : ℝ := 1 / ((n:ℝ)+1)
private lemma eps_pos (n : ℕ) : 0 < eps n := by unfold eps; positivity

private lemma reg_limits (i : Fin 3) {y : RSpace} (hy : y ≠ 0) :
    Tendsto (fun n => regular (eps n) y) atTop (𝓝 (newtonKernel y)) ∧
    Tendsto (fun n => regularGradient (eps n) i y) atTop (𝓝 (newtonGradientKernel i y)) := by
  have he : Tendsto eps atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hr : Tendsto (fun n => Real.sqrt (eps n + normSq3 y)) atTop (𝓝 (euclideanNorm3 y)) := by
    simpa only [zero_add, euclideanNorm3] using (he.add_const (normSq3 y)).sqrt
  have ha : 0 < euclideanNorm3 y := (norm_pos_iff.mpr hy).trans_le (norm_le_newton_radius y)
  have hC : 0 < 4*Real.pi := by positivity
  exact ⟨(hr.const_mul (4*Real.pi)).inv₀ (mul_ne_zero hC.ne' ha.ne'),
    tendsto_const_nhds.div ((hr.pow 3).const_mul (4*Real.pi))
      (mul_ne_zero hC.ne' (pow_ne_zero _ ha.ne'))⟩

private lemma grad_locally_integrable (i : Fin 3) :
    LocallyIntegrable (newtonGradientKernel i) volume := by
  have hd : Module.finrank ℝ RSpace = 3 := Module.finrank_fin_fun ℝ
  apply locallyIntegrable_of_norm_le_rpow (E := RSpace) (μ := volume)
    (f := newtonGradientKernel i) (C := (1:ℝ)) (α := (2:ℝ))
    (by rw [hd]; decide) (by rw [hd]; norm_num)
  · apply Eventually.of_forall
    intro x
    simpa only [one_mul, Real.rpow_neg (norm_nonneg x), Real.rpow_two]
      using newtonGradientKernel_majorized i x
  · exact (newtonGradientKernel_measurable i).aestronglyMeasurable

private lemma cutoff_limit {A : ℕ → RSpace → ℝ} {K φ : RSpace → ℝ}
    (hA : ∀ n, Continuous (A n)) (hφ : Continuous φ)
    (hi : Integrable (fun y => K y * φ y))
    (hdom : ∀ n x, x ≠ 0 → ‖A n x‖ ≤ ‖K x‖)
    (hlim : ∀ x, x ≠ 0 → Tendsto (fun n => A n x) atTop (𝓝 (K x))) :
    Tendsto (fun n => ∫ x, A n x * φ x) atTop (𝓝 (∫ x, K x * φ x)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => ‖K x * φ x‖)
  · intro n
    exact ((hA n).mul hφ).aestronglyMeasurable
  · exact hi.norm
  · intro n
    filter_upwards [(volume : Measure RSpace).ae_ne 0] with x hx
    rw [norm_mul, norm_mul]
    exact mul_le_mul_of_nonneg_right (hdom n x hx) (norm_nonneg _)
  · filter_upwards [(volume : Measure RSpace).ae_ne 0] with x hx
    exact (hlim x hx).mul_const (φ x)

private theorem reg_product_integrable {A K φ : RSpace → ℝ}
    (hA : Continuous A) (hφ : Continuous φ) (hi : Integrable (fun x => K x * φ x))
    (hdom : ∀ x, x ≠ 0 → ‖A x‖ ≤ ‖K x‖) : Integrable (fun x => A x * φ x) := by
  apply hi.norm.mono' (hA.mul hφ).aestronglyMeasurable
  filter_upwards [(volume : Measure RSpace).ae_ne 0] with y hy
  change ‖A y * φ y‖ ≤ ‖K y * φ y‖
  simpa only [norm_mul] using
    (mul_le_mul_of_nonneg_right (hdom y hy) (norm_nonneg (φ y)))

/-- Global integration by parts for the genuine singular coordinate kernel,
whenever the test products in the identity and in the product rule are integrable. -/
theorem wji_newtonKernel_weak_gradient_of_integrable (i : Fin 3) {φ : RSpace → ℝ}
    (hφ : ContDiff ℝ ∞ φ)
    (h0 : Integrable (fun y => newtonKernel y * φ y))
    (hD : Integrable (fun y => newtonKernel y * D i φ y))
    (hG : Integrable (fun y => newtonGradientKernel i y * φ y)) :
    (∫ y, newtonKernel y * D i φ y) = -(∫ y, newtonGradientKernel i y * φ y) := by
  have hφd : ContDiff ℝ ∞ (D i φ) :=
    (contDiff_clm_apply_iff.mp (contDiff_infty_iff_fderiv.mp hφ).2) (basisDirection i)
  have h₁ := cutoff_limit (fun n => (reg_smooth (eps_pos n)).continuous) hφd.continuous hD
    (fun n y hy => (reg_bounds (eps_pos n) i hy).1) (fun y hy => (reg_limits i hy).1)
  have h₂ := cutoff_limit (fun n => reg_grad_cont (eps_pos n) i) hφ.continuous hG
    (fun n y hy => (reg_bounds (eps_pos n) i hy).2) (fun y hy => (reg_limits i hy).2)
  have he (n : ℕ) : (∫ y, regular (eps n) y * D i φ y) =
      -(∫ y, regularGradient (eps n) i y * φ y) := by
    let f := regular (eps n)
    have hfs : ContDiff ℝ ∞ f := reg_smooth (eps_pos n)
    have hd : (fun y => fderiv ℝ f y (basisDirection i)) = regularGradient (eps n) i :=
      funext (regular_partial (eps_pos n) i)
    have h1 : Integrable (fun y => fderiv ℝ f y (basisDirection i) * φ y) := by
      have hi : Integrable ((regularGradient (eps n) i) * φ) :=
        reg_product_integrable (reg_grad_cont (eps_pos n) i) hφ.continuous hG
          (fun _ hy => (reg_bounds (eps_pos n) i hy).2)
      exact (congrArg (fun d : RSpace → ℝ => Integrable (d * φ)) hd).mpr hi
    have h2 : Integrable (fun y => f y * fderiv ℝ φ y (basisDirection i)) :=
      reg_product_integrable hfs.continuous hφd.continuous hD
        (fun _ hy => (reg_bounds (eps_pos n) i hy).1)
    have h3 : Integrable (fun y => f y * φ y) :=
      reg_product_integrable hfs.continuous hφ.continuous h0
        (fun _ hy => (reg_bounds (eps_pos n) i hy).1)
    have hid := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (v := basisDirection i)
      h1 h2 h3 (fun y _ => (contDiff_infty_iff_fderiv.mp hfs).1 y)
      (fun y _ => (contDiff_infty_iff_fderiv.mp hφ).1 y)
    change (∫ y, f y * fderiv ℝ φ y (basisDirection i)) = _
    calc
      _ = -(∫ y, fderiv ℝ f y (basisDirection i) * φ y) := hid
      _ = _ := congrArg (fun d : RSpace → ℝ => -(∫ y, d y * φ y)) hd
  have hsame : (fun n => ∫ y, regular (eps n) y * D i φ y) =
      (fun n => -(∫ y, regularGradient (eps n) i y * φ y)) := funext he
  rw [hsame] at h₁
  exact tendsto_nhds_unique h₁ h₂.neg

/-- The literal coordinate kernel is the distributional derivative of the
Newton potential kernel, including the singularity at zero. -/
theorem wji_newtonKernel_weak_gradient (i : Fin 3) {φ : RSpace → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    (∫ y, newtonKernel y * D i φ y) = -(∫ y, newtonGradientKernel i y * φ y) := by
  have hφd : ContDiff ℝ ∞ (D i φ) :=
    (contDiff_clm_apply_iff.mp (contDiff_infty_iff_fderiv.mp hφ).2) (basisDirection i)
  apply wji_newtonKernel_weak_gradient_of_integrable i hφ
  · exact newtonKernel_locallyIntegrable.integrable_smul_right_of_hasCompactSupport hφ.continuous hc
  · exact newtonKernel_locallyIntegrable.integrable_smul_right_of_hasCompactSupport hφd.continuous
      (hc.fderiv_apply ℝ (basisDirection i))
  · exact (grad_locally_integrable i).integrable_smul_right_of_hasCompactSupport hφ.continuous hc

end
end CondFeffA
