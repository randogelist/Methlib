import WJINewtonSmooth
import WJINewtonSourceParts

namespace CondFeffA

open Fefferman.ConcreteReal MeasureTheory Set Metric Filter
open scoped Topology ContDiff
noncomputable section

private theorem far_newton_partial {g : RSpace → ℝ} (hi : Integrable g)
    {B : ℝ} (hb : ∀ y, ‖g y‖ ≤ B) (x : RSpace)
    (hz : ∀ y ∈ closedBall x 2, g y = 0) (i : Fin 3) :
    spatialDerivative i (newtonPotential g) x =
      ∫ y, g y * newtonGradientKernel i (x-y) := by
  obtain ⟨hJ, hF⟩ := wji_far_potential_derivative hi hb x hz
  change (fderiv ℝ (newtonPotential g) x) (basisDirection i) = _
  rw [hF.fderiv, ContinuousLinearMap.integral_apply hJ]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro y
  change g y * spatialDerivative i newtonKernel (x-y) = _
  by_cases hy : x-y = 0
  · have he : x = y := sub_eq_zero.mp hy
    subst y
    simp only [hz x (mem_closedBall_self (by norm_num : (0:ℝ) ≤ 2)), zero_mul]
  · rw [wji_newtonKernel_partial_of_ne_zero i hy]

/-- Pointwise formula on smooth bounded L¹ sources, allowing their supports
to extend to spatial infinity. -/
theorem wji_partial_newton_eq_kernel_of_smooth (i : Fin 3) {g : RSpace → ℝ}
    (hg : ContDiff ℝ ∞ g) (hi : Integrable g) {A : ℝ} (hA : ∀ y, ‖g y‖ ≤ A) (x : RSpace) :
    spatialDerivative i (newtonPotential g) x = ∫ y, g y * newtonGradientKernel i (x-y) := by
  let η : ContDiffBump x := ⟨2, 3, by norm_num, by norm_num⟩
  let near (y : RSpace) := η y * g y
  let far (y : RSpace) := g y - near y
  have hn : ContDiff ℝ ∞ near := η.contDiff.mul hg
  have hnc : HasCompactSupport near := η.hasCompactSupport.mul_right
  have hni : Integrable near := hn.continuous.integrable_of_hasCompactSupport hnc
  have hfi : Integrable far := hi.sub hni
  have hnb (y : RSpace) : ‖near y‖ ≤ A := by
    change ‖η y * g y‖ ≤ A
    rw [norm_mul, Real.norm_of_nonneg (η.nonneg' y)]
    exact (mul_le_of_le_one_left (norm_nonneg _) (η.le_one (x := y))).trans (hA y)
  have hfb (y : RSpace) : ‖far y‖ ≤ A+A := (norm_sub_le _ _).trans (add_le_add (hA y) (hnb y))
  have hzero (y : RSpace) (hy : y ∈ closedBall x 2) : far y = 0 := by
    change g y - η y * g y = 0
    rw [η.one_of_mem_closedBall hy, one_mul, sub_self]
  have split : newtonPotential g = newtonPotential near + newtonPotential far := by
    funext z
    have he := newtonPotential_sub_on_bounded_L1 hi hni hA hnb z
    change newtonPotential far z = newtonPotential g z - newtonPotential near z at he
    change newtonPotential g z = newtonPotential near z + newtonPotential far z
    linarith
  have h1 : (1 : ℕ∞ω) ≤ ∞ :=
    WithTop.coe_le_coe.mpr (le_top : (1 : ℕ∞) ≤ ⊤)
  have hnd : DifferentiableAt ℝ (newtonPotential near) x :=
    (newtonPotential_compact_hasFDerivAt hnc (hn.of_le h1) x).differentiableAt
  have hfd := (wji_far_potential_derivative hfi hfb x hzero).2.differentiableAt
  have contD : Continuous (spatialDerivative i near) :=
    (hn.continuous_fderiv (by simp)).clm_apply continuous_const
  have compactD : HasCompactSupport (spatialDerivative i near) :=
    hnc.fderiv_apply ℝ (basisDirection i)
  obtain ⟨M, hM⟩ := contD.bounded_above_of_compact_support compactD
  have hnear : spatialDerivative i (newtonPotential near) x =
      ∫ y, near y * newtonGradientKernel i (x-y) := by
    rw [newtonPotential_compact_partial hnc (hn.of_le h1) i x]
    exact wji_newtonPotential_partial_source_parts i hn hni
      (contD.integrable_of_hasCompactSupport compactD) hnb hM x
  have sumD : spatialDerivative i (newtonPotential g) x =
      spatialDerivative i (newtonPotential near) x + spatialDerivative i (newtonPotential far) x := by
    rw [split]
    change (fderiv ℝ (newtonPotential near + newtonPotential far) x) (basisDirection i) = _
    rw [fderiv_add hnd hfd] <;> rfl
  rw [sumD, hnear, far_newton_partial hfi hfb x hzero i,
    ← integral_add (newtonGradientIntegrand_integrable hni hnb i x)
      (newtonGradientIntegrand_integrable hfi hfb i x)]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro y
  change near y * newtonGradientKernel i (x-y) + (g y - near y) * newtonGradientKernel i (x-y) =
    g y * newtonGradientKernel i (x-y)
  ring

theorem wji_partial_newton_eq_newton_partial (i : Fin 3) {g : RSpace → ℝ}
    (hg : ContDiff ℝ ∞ g) (hi : Integrable g) (hd : Integrable (spatialDerivative i g))
    {A B : ℝ} (hA : ∀ y, ‖g y‖ ≤ A) (hB : ∀ y, ‖spatialDerivative i g y‖ ≤ B)
    (x : RSpace) : spatialDerivative i (newtonPotential g) x =
      newtonPotential (spatialDerivative i g) x :=
  (wji_partial_newton_eq_kernel_of_smooth i hg hi hA x).trans
    (wji_newtonPotential_partial_source_parts i hg hi hd hA hB x).symm

end
end CondFeffA
