import CondRecurrence
import Mathlib.Analysis.SpecialFunctions.Pow.Integral

namespace CondFeffA

open Fefferman.ConcreteReal MeasureTheory Set Metric Filter
open scoped Topology
noncomputable section

theorem norm_le_newton_radius (z : RSpace) : ‖z‖ ≤ euclideanNorm3 z := by
  apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2
  intro i
  rw [Real.norm_eq_abs]
  apply Real.le_sqrt_of_sq_le
  rw [sq_abs]
  fin_cases i
  · change (z 0)^2 ≤ z 0 * z 0 + z 1 * z 1 + z 2 * z 2
    nlinarith only [sq_nonneg (z 1), sq_nonneg (z 2)]
  · change (z 1)^2 ≤ z 0 * z 0 + z 1 * z 1 + z 2 * z 2
    nlinarith only [sq_nonneg (z 0), sq_nonneg (z 2)]
  · change (z 2)^2 ≤ z 0 * z 0 + z 1 * z 1 + z 2 * z 2
    nlinarith only [sq_nonneg (z 0), sq_nonneg (z 1)]

/-- A common local majorant for the Newton kernel (k=1) and its coordinate
gradient kernel (k=2). The PDE uses Lebesgue measure on `Fin 3 → ℝ`. -/
def newtonLocalMajorant (k : ℕ) : RSpace → ℝ :=
  (ball (0 : RSpace) 1).indicator (fun z => (‖z‖^k)⁻¹)

def newtonLocalMass (k : ℕ) : ℝ := ∫ z, newtonLocalMajorant k z

theorem newtonLocalMajorant_integrable {k : ℕ} (hk : k < 3) :
    Integrable (newtonLocalMajorant k) := by
  unfold newtonLocalMajorant
  apply IntegrableOn.integrable_indicator _ measurableSet_ball
  have hd : Module.finrank ℝ RSpace = 3 := Module.finrank_fin_fun ℝ
  apply integrableOn_ball_of_norm_le_rpow (E := RSpace) (μ := volume)
    (f := fun z : RSpace => (‖z‖^k)⁻¹) (r := 1) (C := (1 : ℝ)) (α := (k : ℝ))
    (by rw [hd]; decide) (by rw [hd]; exact_mod_cast hk)
  · apply Filter.Eventually.of_forall
    intro z
    simpa only [Real.norm_of_nonneg (by positivity : 0 ≤ (‖z‖^k)⁻¹), one_mul,
      Real.rpow_neg (norm_nonneg z), Real.rpow_natCast] using le_refl ((‖z‖^k)⁻¹)
  · exact (continuous_norm.measurable.pow_const k).inv.aestronglyMeasurable

private def kernelMajorantAt (k : ℕ) (g : RSpace → ℝ) (M : ℝ) (x : RSpace) :=
  fun y : RSpace => M * newtonLocalMajorant k (x-y) + ‖g y‖

private theorem kernel_majorant_integrable {k : ℕ} (hk : k < 3)
    {g : RSpace → ℝ} (hg : Integrable g) (M : ℝ) (x : RSpace) :
    Integrable (kernelMajorantAt k g M x) :=
  (((newtonLocalMajorant_integrable hk).comp_sub_left x).const_mul M).add hg.norm

private theorem kernel_majorant_bound {k : ℕ} {K g : RSpace → ℝ} {M : ℝ}
    (hK : ∀ z, ‖K z‖ ≤ (‖z‖^k)⁻¹) (hb : ∀ y, ‖g y‖ ≤ M) (x y : RSpace) :
    ‖g y * K (x-y)‖ ≤ kernelMajorantAt k g M x y := by
  rw [norm_mul]
  by_cases h : x - y ∈ ball (0 : RSpace) 1
  · simp only [kernelMajorantAt, newtonLocalMajorant, indicator_of_mem h]
    exact (mul_le_mul (hb y) (hK _) (norm_nonneg _) ((norm_nonneg _).trans (hb y))).trans
      (le_add_of_nonneg_right (norm_nonneg _))
  · simp only [kernelMajorantAt, newtonLocalMajorant, indicator_of_notMem h, mul_zero, zero_add]
    have hout : 1 ≤ ‖x-y‖ := le_of_not_gt (fun hh => h (mem_ball_zero_iff.mpr hh))
    have hone : ‖K (x-y)‖ ≤ 1 := (hK _).trans (inv_le_one_of_one_le₀ (one_le_pow₀ hout))
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hone (norm_nonneg (g y))

/-- An integrable bounded source times a reciprocal-power kernel. The
power is below the spatial dimension. Bounds at infinity use only L¹. -/
theorem integrable_newton_majorized {k : ℕ} (hk : k < 3) {K g : RSpace → ℝ}
    (hmeas : Measurable K) (hK : ∀ z, ‖K z‖ ≤ (‖z‖^k)⁻¹) (hg : Integrable g)
    {M : ℝ} (hb : ∀ y, ‖g y‖ ≤ M) (x : RSpace) :
    Integrable (fun y => g y * K (x-y)) := by
  apply (kernel_majorant_integrable hk hg M x).mono'
  · apply AEMeasurable.aestronglyMeasurable
    exact hg.aemeasurable.mul ((hmeas.comp (measurable_const.sub measurable_id)).aemeasurable)
  · exact Filter.Eventually.of_forall (kernel_majorant_bound hK hb x)

theorem integral_newton_majorized_le {k : ℕ} (hk : k < 3) {K g : RSpace → ℝ}
    (hmeas : Measurable K) (hK : ∀ z, ‖K z‖ ≤ (‖z‖^k)⁻¹) (hg : Integrable g)
    {M : ℝ} (hb : ∀ y, ‖g y‖ ≤ M) (x : RSpace) :
    ‖∫ y, g y * K (x-y)‖ ≤ M * newtonLocalMass k + ∫ y, ‖g y‖ := by
  have hi := integrable_newton_majorized hk hmeas hK hg hb x
  have hl := (newtonLocalMajorant_integrable hk).comp_sub_left x
  calc
    _ ≤ ∫ y, ‖g y * K (x-y)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ y, kernelMajorantAt k g M x y :=
      integral_mono hi.norm (kernel_majorant_integrable hk hg M x) (kernel_majorant_bound hK hb x)
    _ = _ := by
      unfold kernelMajorantAt
      rw [integral_add (hl.const_mul M) hg.norm, integral_const_mul,
        integral_sub_left_eq_self (newtonLocalMajorant k) volume x] <;> rfl

def newtonKernel (z : RSpace) : ℝ := (4 * Real.pi * euclideanNorm3 z)⁻¹

theorem newtonKernel_measurable : Measurable newtonKernel := by
  unfold newtonKernel euclideanNorm3 normSq3
  fun_prop

theorem newtonKernel_majorized (z : RSpace) :
    ‖newtonKernel z‖ ≤ (‖z‖^(1 : ℕ))⁻¹ := by
  rw [pow_one]
  by_cases hz : z = 0
  · subst z
    simp [newtonKernel, euclideanNorm3, normSq3]
  have he : 0 ≤ euclideanNorm3 z := Real.sqrt_nonneg _
  have hp : (1 : ℝ) ≤ 4 * Real.pi := by linarith [Real.pi_gt_three]
  have hden : ‖z‖ ≤ 4 * Real.pi * euclideanNorm3 z := calc
    _ ≤ euclideanNorm3 z := norm_le_newton_radius z
    _ = 1 * euclideanNorm3 z := (one_mul _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right hp he
  have hden0 : 0 ≤ 4 * Real.pi * euclideanNorm3 z := le_trans (norm_nonneg z) hden
  rw [newtonKernel, Real.norm_of_nonneg (inv_nonneg.mpr hden0)]
  exact inv_anti₀ (norm_pos_iff.mpr hz) hden

theorem newtonIntegrand_integrable {g : RSpace → ℝ} (hg : Integrable g)
    {M : ℝ} (hb : ∀ y, ‖g y‖ ≤ M) (x : RSpace) :
    Integrable (fun y => g y / (4 * Real.pi * euclideanNorm3 (x-y))) := by
  simpa only [div_eq_mul_inv, newtonKernel] using
    integrable_newton_majorized (k := 1) (by decide) newtonKernel_measurable
      newtonKernel_majorized hg hb x

/-- Uniform estimate at every spatial point, with the actual integral in
`CondRecurrence`. The constant is independent of the evaluation point. -/
theorem newtonPotential_norm_le {g : RSpace → ℝ} (hg : Integrable g)
    {M : ℝ} (hb : ∀ y, ‖g y‖ ≤ M) (x : RSpace) :
    ‖newtonPotential g x‖ ≤ M * newtonLocalMass 1 + ∫ y, ‖g y‖ := by
  simpa only [newtonPotential, div_eq_mul_inv, newtonKernel] using
    integral_newton_majorized_le (k := 1) (by decide) newtonKernel_measurable
      newtonKernel_majorized hg hb x

theorem newtonPotential_sub_on_bounded_L1 {g h : RSpace → ℝ}
    (hg : Integrable g) (hh : Integrable h) {G H : ℝ}
    (bg : ∀ y, ‖g y‖ ≤ G) (bh : ∀ y, ‖h y‖ ≤ H) (x : RSpace) :
    newtonPotential (g-h) x = newtonPotential g x - newtonPotential h x := by
  simp only [newtonPotential, Pi.sub_apply, sub_div]
  exact integral_sub (newtonIntegrand_integrable hg bg x) (newtonIntegrand_integrable hh bh x)

theorem newtonPotential_error_le {g h : RSpace → ℝ}
    (hg : Integrable g) (hh : Integrable h) {G H C : ℝ}
    (bg : ∀ y, ‖g y‖ ≤ G) (bh : ∀ y, ‖h y‖ ≤ H)
    (herr : ∀ y, ‖g y - h y‖ ≤ C) (x : RSpace) :
    ‖newtonPotential g x - newtonPotential h x‖ ≤
      C * newtonLocalMass 1 + ∫ y, ‖g y - h y‖ := by
  rw [← newtonPotential_sub_on_bounded_L1 hg hh bg bh x]
  exact newtonPotential_norm_le (g := g-h) (hg.sub hh) herr x

/-- Cutoff convergence in L¹ together with a uniform source error tending
    to zero gives uniform convergence of the literal potentials. -/
theorem newtonPotential_tendstoUniformly {g : RSpace → ℝ} {G : ℕ → RSpace → ℝ}
    (hg : Integrable g) (hG : ∀ n, Integrable (G n))
    {B : ℝ} (hb : ∀ y, ‖g y‖ ≤ B)
    {C : ℕ → ℝ} (herr : ∀ n y, ‖G n y - g y‖ ≤ C n)
    (hC : Tendsto C atTop (𝓝 0))
    (hL1 : Tendsto (fun n => ∫ y, ‖G n y - g y‖) atTop (𝓝 0)) :
    TendstoUniformly (fun n => newtonPotential (G n)) (newtonPotential g) atTop := by
  have hbound (n : ℕ) (y : RSpace) : ‖G n y‖ ≤ C n + B := calc
    ‖G n y‖ = ‖(G n y - g y) + g y‖ := by rw [sub_add_cancel]
    _ ≤ ‖G n y - g y‖ + ‖g y‖ := norm_add_le _ _
    _ ≤ _ := add_le_add (herr n y) (hb y)
  have htot : Tendsto (fun n => C n * newtonLocalMass 1 + ∫ y, ‖G n y - g y‖)
      atTop (𝓝 0) := by
    simpa only [zero_mul, zero_add] using (hC.mul_const (newtonLocalMass 1)).add hL1
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [htot.eventually_lt_const hε] with n hn
  intro x
  rw [dist_comm, dist_eq_norm]
  exact (newtonPotential_error_le (hG n) hg (hbound n) hb (herr n) x).trans_lt hn

/-- Only the cutoff potentials need derivative formulas. The L¹/uniform
    source estimates identify the limiting potential before taking fderiv. -/
theorem newtonPotential_partial_of_cutoffs {g : RSpace → ℝ} {G : ℕ → RSpace → ℝ}
    (hg : Integrable g) (hG : ∀ n, Integrable (G n))
    {B : ℝ} (hb : ∀ y, ‖g y‖ ≤ B)
    {C : ℕ → ℝ} (herr : ∀ n y, ‖G n y - g y‖ ≤ C n)
    (hC : Tendsto C atTop (𝓝 0))
    (hL1 : Tendsto (fun n => ∫ y, ‖G n y - g y‖) atTop (𝓝 0))
    {D : RSpace → RSpace →L[ℝ] ℝ} {Dn : ℕ → RSpace → RSpace →L[ℝ] ℝ}
    (hd : ∀ n x, HasFDerivAt (newtonPotential (G n)) (Dn n x) x)
    (hD : TendstoUniformly Dn D atTop) (i : Fin 3) (x : RSpace) :
    spatialDerivative i (newtonPotential g) x = D x (basisDirection i) := by
  have hlim := newtonPotential_tendstoUniformly hg hG hb herr hC hL1
  have hder := hasFDerivAt_of_tendstoUniformly hD hd hlim.tendsto_at x
  exact congrArg (fun A : RSpace →L[ℝ] ℝ => A (basisDirection i)) hder.fderiv

/-- Explicit coordinate kernel for the proposed Newton gradient. The
    next two lemmas concern its convolution; identifying that convolution
    with a spatial derivative is a separate theorem. -/
def newtonGradientKernel (i : Fin 3) (z : RSpace) : ℝ :=
  -z i / (4 * Real.pi * euclideanNorm3 z ^ 3)

theorem newtonGradientKernel_measurable (i : Fin 3) :
    Measurable (newtonGradientKernel i) := by
  unfold newtonGradientKernel euclideanNorm3 normSq3
  fun_prop

theorem newtonGradientKernel_majorized (i : Fin 3) (z : RSpace) :
    ‖newtonGradientKernel i z‖ ≤ (‖z‖^2)⁻¹ := by
  by_cases hz : z = 0
  · subst z
    simp [newtonGradientKernel, euclideanNorm3, normSq3]
  let e := euclideanNorm3 z
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hne : ‖z‖ ≤ e := norm_le_newton_radius z
  have he : 0 < e := hn.trans_le hne
  have hcoord : ‖z i‖ ≤ e := (norm_le_pi_norm z i).trans hne
  have hr : 1 ≤ 4 * Real.pi := by linarith [Real.pi_pos, Real.two_le_pi]
  have hd : 0 < 4 * Real.pi * e ^ 3 := by positivity
  change ‖-z i / (4 * Real.pi * e ^ 3)‖ ≤ (‖z‖^2)⁻¹
  rw [norm_div, norm_neg, Real.norm_of_nonneg hd.le]
  calc
    _ ≤ e / (4 * Real.pi * e ^ 3) := div_le_div_of_nonneg_right hcoord hd.le
    _ = (4 * Real.pi)⁻¹ * (e^2)⁻¹ := by
      field_simp [Real.pi_ne_zero, he.ne'] <;> ring
    _ ≤ 1 * (‖z‖^2)⁻¹ :=
      mul_le_mul (inv_le_one_of_one_le₀ hr)
        (inv_anti₀ (sq_pos_of_pos hn) (pow_le_pow_left₀ hn.le hne 2))
        (by positivity) zero_le_one
    _ = _ := one_mul _

theorem newtonGradientIntegrand_integrable {g : RSpace → ℝ} (hg : Integrable g)
    {M : ℝ} (hb : ∀ y, ‖g y‖ ≤ M) (i : Fin 3) (x : RSpace) :
    Integrable (fun y => g y * newtonGradientKernel i (x-y)) :=
  integrable_newton_majorized (k := 2) (by decide) (newtonGradientKernel_measurable i)
    (newtonGradientKernel_majorized i) hg hb x

theorem newtonGradientIntegral_norm_le {g : RSpace → ℝ} (hg : Integrable g)
    {M : ℝ} (hb : ∀ y, ‖g y‖ ≤ M) (i : Fin 3) (x : RSpace) :
    ‖∫ y, g y * newtonGradientKernel i (x-y)‖ ≤ M * newtonLocalMass 2 + ∫ y, ‖g y‖ :=
  integral_newton_majorized_le (k := 2) (by decide) (newtonGradientKernel_measurable i)
    (newtonGradientKernel_majorized i) hg hb x

end
end CondFeffA
