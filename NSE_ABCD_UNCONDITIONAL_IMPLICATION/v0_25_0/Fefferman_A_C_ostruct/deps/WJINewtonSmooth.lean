import WJINewtonDifferentiate
import WJINewtonPoisson
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace CondFeffA

open Fefferman.ConcreteReal MeasureTheory Set Metric Filter
open scoped Topology ContDiff BigOperators
noncomputable section

private def euclideanMap : RSpace →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm.toContinuousLinearMap

private theorem radius_eq_norm (z : RSpace) : euclideanNorm3 z = ‖euclideanMap z‖ := by
  rw [EuclideanSpace.norm_eq]
  change Real.sqrt (z 0 * z 0 + z 1 * z 1 + z 2 * z 2) =
    Real.sqrt (∑ i : Fin 3, ‖z i‖ ^ 2)
  simp only [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs]
  simp only [pow_two]

private theorem radius_sub_bound (v w : RSpace) :
    |euclideanNorm3 v - euclideanNorm3 w| ≤ ‖euclideanMap‖ * ‖v-w‖ := by
  rw [radius_eq_norm, radius_eq_norm]
  exact (abs_norm_sub_norm_le _ _).trans (by
    rw [← map_sub]
    exact euclideanMap.le_opNorm _)

private theorem kernel_diff {z : RSpace} (hz : 0 < euclideanNorm3 z) :
    DifferentiableAt ℝ newtonKernel z := by
  have hn : euclideanMap z ≠ 0 := by
    intro h
    rw [radius_eq_norm, h, norm_zero] at hz
    exact (lt_irrefl 0 hz)
  have hrad : DifferentiableAt ℝ euclideanNorm3 z := by
    rw [show euclideanNorm3 = (fun a => ‖euclideanMap a‖) from funext radius_eq_norm]
    exact euclideanMap.differentiableAt.norm ℝ hn
  have hden : DifferentiableAt ℝ (fun a : RSpace => (4 * Real.pi) * euclideanNorm3 a) z :=
    hrad.const_mul (4 * Real.pi)
  change DifferentiableAt ℝ (fun a : RSpace => ((4 * Real.pi) * euclideanNorm3 a)⁻¹) z
  exact hden.inv (mul_ne_zero (by positivity : (4 : ℝ) * Real.pi ≠ 0) hz.ne')

private def farBound : ℝ := (4 * Real.pi) * ‖euclideanMap‖

private theorem kernel_difference_bound {a b : RSpace}
    (ha : 1 ≤ euclideanNorm3 a) (hb : 1 ≤ euclideanNorm3 b) :
    ‖newtonKernel a - newtonKernel b‖ ≤ farBound * ‖a-b‖ := by
  have hp : (1 : ℝ) ≤ 4 * Real.pi := by linarith [Real.pi_gt_three]
  let d (z : RSpace) := (4 * Real.pi) * euclideanNorm3 z
  have ha' : 1 ≤ d a := one_le_mul_of_one_le_of_one_le hp ha
  have hb' : 1 ≤ d b := one_le_mul_of_one_le_of_one_le hp hb
  have hd : 0 < d a * d b := mul_pos (zero_lt_one.trans_le ha') (zero_lt_one.trans_le hb')
  calc
    ‖newtonKernel a - newtonKernel b‖ = |d a - d b| / (d a * d b) := by
      change |(d a)⁻¹ - (d b)⁻¹| = _
      rw [inv_sub_inv (zero_lt_one.trans_le ha').ne' (zero_lt_one.trans_le hb').ne',
        abs_div, abs_of_pos hd, abs_sub_comm (d b) (d a)]
    _ ≤ |d a - d b| := div_le_self (abs_nonneg _) (one_le_mul_of_one_le_of_one_le ha' hb')
    _ = (4 * Real.pi) * |euclideanNorm3 a - euclideanNorm3 b| := by
      simp only [d, ← mul_sub, abs_mul, abs_of_pos (zero_lt_one.trans_le hp)]
    _ ≤ (4 * Real.pi) * (‖euclideanMap‖ * ‖a-b‖) :=
      mul_le_mul_of_nonneg_left (radius_sub_bound a b) (zero_lt_one.trans_le hp).le
    _ = _ := by
      unfold farBound
      exact (mul_assoc (4 * Real.pi) ‖euclideanMap‖ ‖a-b‖).symm

/-- On a unit neighborhood of x₀, an L¹ source vanishing in its double
ball is separated from the Newton singularity, uniformly in the integral variable. -/
theorem wji_far_potential_derivative {g : RSpace → ℝ} (hi : Integrable g) {B : ℝ}
    (hb : ∀ y, ‖g y‖ ≤ B) (x₀ : RSpace)
    (hz : ∀ y ∈ closedBall x₀ 2, g y = 0) :
    Integrable (fun y => g y • fderiv ℝ newtonKernel (x₀-y)) ∧
      HasFDerivAt (newtonPotential g) (∫ y, g y • fderiv ℝ newtonKernel (x₀-y)) x₀ := by
  let U := ball x₀ (1 : ℝ)
  let F (x y : RSpace) := g y * newtonKernel (x-y)
  let J (y : RSpace) := g y • fderiv ℝ newtonKernel (x₀-y)
  let bound (y : RSpace) := ‖g y‖ * farBound
  have sep {y x : RSpace} (hy : g y ≠ 0) (hx : x ∈ U) : 1 ≤ euclideanNorm3 (x-y) := by
    have hyo : 2 < dist y x₀ := lt_of_not_ge (fun he => hy (hz y (mem_closedBall.mpr he)))
    have hxo : dist x x₀ < 1 := mem_ball.mp hx
    have htri := dist_triangle y x x₀
    have hh : 1 ≤ dist x y := by rw [dist_comm x y]; linarith
    exact (by simpa only [dist_eq_norm] using hh : 1 ≤ ‖x-y‖).trans (norm_le_newton_radius _)
  have hx₀ : x₀ ∈ U := mem_ball_self zero_lt_one
  have hi₀ : Integrable (F x₀) := by
    simpa only [F, newtonKernel, div_eq_mul_inv] using newtonIntegrand_integrable hi hb x₀
  have hF (x : RSpace) : AEStronglyMeasurable (F x) volume :=
    (hi.aemeasurable.mul ((newtonKernel_measurable.comp
      (measurable_const.sub measurable_id)).aemeasurable)).aestronglyMeasurable
  have hJ : AEStronglyMeasurable J volume :=
    (hi.aemeasurable.smul (((measurable_fderiv ℝ newtonKernel).comp
      (measurable_const.sub measurable_id)).aemeasurable)).aestronglyMeasurable
  have hLip : ∀ᵐ y : RSpace, ∀ x ∈ U, ‖F x y - F x₀ y‖ ≤ bound y * ‖x-x₀‖ := by
    apply Eventually.of_forall
    intro y x hx
    by_cases hy : g y = 0
    · simp [F, bound, hy]
    have hk := kernel_difference_bound (sep hy hx) (sep hy hx₀)
    rw [show (x-y)-(x₀-y) = x-x₀ by abel] at hk
    change ‖g y * newtonKernel (x-y) - g y * newtonKernel (x₀-y)‖ ≤
      (‖g y‖ * farBound) * ‖x-x₀‖
    rw [← mul_sub, norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left hk (norm_nonneg _)
  have hdiff : ∀ᵐ y : RSpace, HasFDerivAt (fun x => F x y) (J y) x₀ := by
    apply Eventually.of_forall
    intro y
    by_cases hy : g y = 0
    · simpa only [F, J, hy, zero_mul, zero_smul] using
        (hasFDerivAt_const (0 : ℝ) x₀)
    have hd := (kernel_diff (zero_lt_one.trans_le (sep hy hx₀))).hasFDerivAt
    have hshift : HasFDerivAt (fun x : RSpace => newtonKernel (x-y))
        (fderiv ℝ newtonKernel (x₀-y)) x₀ := by
      simpa only [Function.comp_def, ContinuousLinearMap.comp_id] using
        hd.comp x₀ (hasFDerivAt_sub_const (𝕜 := ℝ) (x := x₀) y)
    change HasFDerivAt (fun x : RSpace => g y * newtonKernel (x-y))
      (g y • fderiv ℝ newtonKernel (x₀-y)) x₀
    exact hshift.const_mul (g y)
  have h := hasFDerivAt_integral_of_dominated_loc_of_lip' (μ := volume) (F := F)
    (F' := J) (s := U) (bound := bound) (ball_mem_nhds x₀ zero_lt_one)
    (fun x _ => hF x) hi₀ hJ hLip (hi.norm.mul_const farBound) hdiff
  refine ⟨h.1, ?_⟩
  have hpotential : newtonPotential g = fun x => ∫ y, F x y := by
    funext x
    simp only [newtonPotential, F, newtonKernel, div_eq_mul_inv]
  rw [hpotential]
  change HasFDerivAt (fun x => ∫ y, F x y) (∫ y, J y) x₀
  exact h.2

/-- Smooth L¹ sources that are globally bounded give differentiable Newton
potentials. Only local smoothness is used in the near part. -/
theorem newtonPotential_differentiable_of_smooth_bounded_L1 {g : RSpace → ℝ}
    (hg : ContDiff ℝ ∞ g) (hi : Integrable g) {B : ℝ} (hb : ∀ y, ‖g y‖ ≤ B) :
    Differentiable ℝ (newtonPotential g) := by
  intro x₀
  let η : ContDiffBump x₀ := ⟨2, 3, by norm_num, by norm_num⟩
  let g₀ (y : RSpace) := η y * g y
  let g₁ (y : RSpace) := g y - g₀ y
  have h₀ : ContDiff ℝ ∞ g₀ := η.contDiff.mul hg
  have hc₀ : HasCompactSupport g₀ := η.hasCompactSupport.mul_right
  have hi₀ : Integrable g₀ := h₀.continuous.integrable_of_hasCompactSupport hc₀
  have hi₁ : Integrable g₁ := hi.sub hi₀
  have hb₀ (y : RSpace) : ‖g₀ y‖ ≤ B := by
    change ‖η y * g y‖ ≤ B
    rw [norm_mul, Real.norm_of_nonneg (η.nonneg' y)]
    exact (mul_le_of_le_one_left (norm_nonneg _) (η.le_one (x := y))).trans (hb y)
  have hb₁ (y : RSpace) : ‖g₁ y‖ ≤ B+B := (norm_sub_le _ _).trans (add_le_add (hb y) (hb₀ y))
  have hvan (y : RSpace) (hy : y ∈ closedBall x₀ 2) : g₁ y = 0 := by
    change g y - η y * g y = 0
    rw [η.one_of_mem_closedBall hy, one_mul, sub_self]
  have hsplit : newtonPotential g = newtonPotential g₀ + newtonPotential g₁ := by
    funext x
    have hsub := newtonPotential_sub_on_bounded_L1 hi hi₀ hb hb₀ x
    change newtonPotential g x = newtonPotential g₀ x + newtonPotential g₁ x
    change newtonPotential g₁ x = newtonPotential g x - newtonPotential g₀ x at hsub
    linarith
  rw [hsplit]
  exact ((newtonPotential_compact_contDiff (k := ⊤) hc₀ h₀).differentiable (by simp) x₀).add
    (wji_far_potential_derivative hi₁ hb₁ x₀ hvan).2.differentiableAt

theorem wjiNewtonScalar_differentiable (v w : WJISobolev.space) :
    Differentiable ℝ (wjiNewtonScalar v.val w.val) := by
  have ht := WJISobolev.transport_mem v w
  have hd (i : Fin 3) := WJISobolev.scalar_partial (ht i) i
  have hg : fieldDiv (transport v.val w.val) ∈ WJISobolev.scalar :=
    WJISobolev.scalar.add_mem (WJISobolev.scalar.add_mem (hd 0) (hd 1)) (hd 2)
  obtain ⟨B, hb⟩ := WJISobolev.transport_div_bounded v w
  exact newtonPotential_differentiable_of_smooth_bounded_L1 (WJISobolev.scalar_smooth hg)
    (WJISobolev.transport_div_integrable v w) hb

end
end CondFeffA
