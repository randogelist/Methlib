import WJINewtonKernel
import WJISobolevSpace
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Function.L2Space

namespace CondFeffA
open Fefferman.ConcreteReal MeasureTheory Set Metric Filter
open scoped RealInnerProductSpace Topology BigOperators
noncomputable section

private theorem inner_toLp_real {f g : RSpace → ℝ}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    inner ℝ (hf.toLp f) (hg.toLp g) = ∫ y, f y * g y := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with y hy hz
  change inner ℝ ((hf.toLp f) y) ((hg.toLp g) y) = f y * g y
  rw [hy, hz, Real.inner_apply]

private theorem integral_cauchy_sq {f g : RSpace → ℝ}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    (∫ y, f y * g y)^2 ≤ (∫ y, (f y)^2) * ∫ y, (g y)^2 := by
  calc
    (∫ y, f y * g y)^2 = |inner ℝ (hf.toLp f) (hg.toLp g)|^2 := by
      rw [sq_abs, inner_toLp_real hf hg]
    _ ≤ (‖hf.toLp f‖ * ‖hg.toLp g‖)^2 :=
      pow_le_pow_left₀ (abs_nonneg _) (abs_real_inner_le_norm (hf.toLp f) (hg.toLp g)) 2
    _ = (∫ y, f y * f y) * ∫ y, g y * g y := by
      rw [mul_pow, ← real_inner_self_eq_norm_sq (hf.toLp f),
        ← real_inner_self_eq_norm_sq (hg.toLp g), inner_toLp_real hf hf, inner_toLp_real hg hg]
    _ = _ := by simp only [pow_two]

private theorem convolution_sq_bound {a b : RSpace → ℝ} (ha : Integrable a)
    (ham : Measurable a) (hbm : Measurable b) {M : ℝ} (hM : ∀ y, ‖b y‖ ≤ M) (x : RSpace) :
    (∫ y, a y * b (x-y))^2 ≤
      (∫ y, ‖a y‖) * ∫ y, ‖a y‖ * (b (x-y))^2 := by
  let U := fun y : RSpace => Real.sqrt ‖a y‖
  let V := fun y : RSpace => U y * ‖b (x-y)‖
  have hb' : Measurable (fun y : RSpace => b (x-y)) :=
    hbm.comp (measurable_const.sub measurable_id)
  have hU : Measurable U := ham.norm.sqrt
  have hV : Measurable V := hU.mul hb'.norm
  have usq (y : RSpace) : U y ^ 2 = ‖a y‖ := Real.sq_sqrt (norm_nonneg _)
  have vsq (y : RSpace) : V y ^ 2 = ‖a y‖ * (b (x-y))^2 := by
    simp only [V, mul_pow, usq, Real.norm_eq_abs, sq_abs]
  have hu : MemLp U 2 volume := by
    apply (memLp_two_iff_integrable_sq hU.aestronglyMeasurable).2
    simpa only [usq] using ha.norm
  have hv : MemLp V 2 volume := by
    apply (memLp_two_iff_integrable_sq hV.aestronglyMeasurable).2
    simp only [vsq]
    apply ha.norm.mul_bdd ((hb'.pow_const 2).aestronglyMeasurable) (c := M^2)
    exact .of_forall fun y => by
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (hM _) 2
  have hint : |∫ y, a y * b (x-y)| ≤ ∫ y, U y * V y := calc
    _ ≤ ∫ y, ‖a y * b (x-y)‖ := norm_integral_le_integral_norm _
    _ = _ := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro y
      change ‖a y * b (x-y)‖ = U y * (U y * ‖b (x-y)‖)
      rw [norm_mul, ← mul_assoc, ← sq, usq]
  calc
    (∫ y, a y * b (x-y))^2 = |∫ y, a y * b (x-y)|^2 := (sq_abs _).symm
    _ ≤ (∫ y, U y * V y)^2 := pow_le_pow_left₀ (abs_nonneg _) hint 2
    _ ≤ _ := by simpa only [usq, vsq] using integral_cauchy_sq hu hv

/-- L¹ * (L² ∩ L∞) belongs to L² on the package's coordinate measure.
The majorant is the L¹ convolution of |a| with b². -/
theorem wji_convolution_memL2 {a b : RSpace → ℝ} (ha : Integrable a)
    (hb : MemLp b 2 volume) (ham : Measurable a) (hbm : Measurable b)
    {M : ℝ} (hM : ∀ y, ‖b y‖ ≤ M) :
    MemLp (fun x => ∫ y, a y * b (x-y)) 2 volume := by
  have hmeas : AEStronglyMeasurable (fun x => ∫ y, a y * b (x-y)) volume :=
    (ha.aestronglyMeasurable.convolution_integrand
      (ContinuousLinearMap.mul ℝ ℝ) hb.aestronglyMeasurable).integral_prod_right'
  have hmaj : Integrable
      (fun x : RSpace => (∫ y, ‖a y‖) * ∫ y, ‖a y‖ * (b (x-y))^2) :=
    (ha.norm.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ) hb.integrable_sq).const_mul _
  apply (memLp_two_iff_integrable_sq hmeas).2
  apply hmaj.mono' ((hmeas.aemeasurable.pow_const 2).aestronglyMeasurable)
  apply Filter.Eventually.of_forall
  intro x
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact convolution_sq_bound ha ham hbm hM x

private def near (i : Fin 3) : RSpace → ℝ :=
  (ball (0 : RSpace) 1).indicator (newtonGradientKernel i)

private def far (i : Fin 3) : RSpace → ℝ :=
  (ball (0 : RSpace) 1)ᶜ.indicator (newtonGradientKernel i)

private theorem near_meas (i : Fin 3) : Measurable (near i) :=
  (newtonGradientKernel_measurable i).indicator measurableSet_ball

private theorem far_meas (i : Fin 3) : Measurable (far i) :=
  (newtonGradientKernel_measurable i).indicator measurableSet_ball.compl

theorem wji_newtonGradient_near_integrable (i : Fin 3) :
    Integrable ((ball (0 : RSpace) 1).indicator (newtonGradientKernel i)) := by
  apply (newtonLocalMajorant_integrable (k := 2) (by decide)).mono' (near_meas i).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro z
  by_cases hz : z ∈ ball (0 : RSpace) 1
  · simpa only [near, newtonLocalMajorant, indicator_of_mem hz] using
      newtonGradientKernel_majorized i z
  · simp only [near, newtonLocalMajorant, indicator_of_notMem hz, norm_zero, le_refl]

private theorem far_le (i : Fin 3) (z : RSpace) : ‖far i z‖ ≤ 1 := by
  by_cases hz : z ∈ (ball (0 : RSpace) 1)ᶜ
  · rw [far, indicator_of_mem hz]
    have hr : 1 ≤ ‖z‖ := le_of_not_gt (fun h => hz (mem_ball_zero_iff.mpr h))
    exact (newtonGradientKernel_majorized i z).trans (inv_le_one_of_one_le₀ (one_le_pow₀ hr))
  · simp [far, hz]

/-- The exterior gradient kernel is square-integrable because its square
decays like |x|⁻⁴ in dimension three. -/
theorem wji_newtonGradient_far_memL2 (i : Fin 3) :
    MemLp ((ball (0 : RSpace) 1)ᶜ.indicator (newtonGradientKernel i)) 2 volume := by
  have hd : Module.finrank ℝ RSpace = 3 := Module.finrank_fin_fun ℝ
  have hw : Integrable (fun z : RSpace => ((1+‖z‖)^4)⁻¹) := by
    have h := integrable_one_add_norm (μ := (volume : Measure RSpace)) (r := 4)
      (by rw [hd]; norm_num)
    have he (z : RSpace) : (1+‖z‖)^(-(4:ℝ)) = ((1+‖z‖)^4)⁻¹ := by
      rw [Real.rpow_neg (by positivity)]
      exact congrArg (fun t : ℝ => t⁻¹) (Real.rpow_natCast (1+‖z‖) 4)
    simpa only [he] using h
  apply (memLp_two_iff_integrable_sq_norm (far_meas i).aestronglyMeasurable).2
  apply (hw.const_mul (16:ℝ)).mono' (((far_meas i).norm.pow_const 2).aestronglyMeasurable)
  apply Filter.Eventually.of_forall
  intro z
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  change ‖far i z‖^2 ≤ 16 * ((1+‖z‖)^4)⁻¹
  by_cases hz : z ∈ (ball (0 : RSpace) 1)ᶜ
  · have hr : 1 ≤ ‖z‖ := le_of_not_gt (fun h => hz (mem_ball_zero_iff.mpr h))
    have hpos : 0 < ‖z‖ := lt_of_lt_of_le zero_lt_one hr
    have hpow : (1 + ‖z‖)^4 ≤ 16 * ‖z‖^4 := calc
      _ ≤ (2*‖z‖)^4 := pow_le_pow_left₀ (by positivity) (by linarith) 4
      _ = _ := by ring
    rw [far, indicator_of_mem hz]
    calc
      _ ≤ ((‖z‖^2)⁻¹)^2 := pow_le_pow_left₀ (norm_nonneg _) (newtonGradientKernel_majorized i z) 2
      _ ≤ 16*((1+‖z‖)^4)⁻¹ := by
        rw [inv_pow, show (‖z‖^2)^2 = ‖z‖^4 by ring]
        have hdiv : 1 / ‖z‖^4 ≤ 16 / (1+‖z‖)^4 :=
          (div_le_div_iff₀ (by positivity) (by positivity)).2 (by simpa only [one_mul] using hpow)
        simpa only [div_eq_mul_inv, one_mul] using hdiv
  · rw [far, indicator_of_notMem hz, norm_zero, zero_pow (by decide : 2 ≠ 0)]
    positivity

theorem wji_convolution_swap (a b : RSpace → ℝ) (x : RSpace) :
    (∫ y, a y * b (x-y)) = ∫ y, b y * a (x-y) := by
  rw [← integral_sub_left_eq_self (fun y : RSpace => a y * b (x-y)) volume x]
  simp only [sub_sub_self, mul_comm]

/-- Full, signed coordinate Newton-gradient convolution maps L¹ ∩ L² ∩ L∞
sources into L², by the local L¹ and exterior L² split. -/
theorem wji_newtonGradient_convolution_memL2 (i : Fin 3) {f : RSpace → ℝ}
    (hf1 : Integrable f) (hf2 : MemLp f 2 volume) (hf : Measurable f)
    {M : ℝ} (hM : ∀ x, ‖f x‖ ≤ M) :
    MemLp (fun x => ∫ y, f y * newtonGradientKernel i (x-y)) 2 volume := by
  have hn := wji_convolution_memL2 (wji_newtonGradient_near_integrable i) hf2 (near_meas i) hf hM
  have ht := wji_convolution_memL2 hf1 (wji_newtonGradient_far_memL2 i) hf (far_meas i) (far_le i)
  have he : (fun x : RSpace => ∫ y, f y * newtonGradientKernel i (x-y)) =
      (fun x => ∫ y, near i y * f (x-y)) + (fun x => ∫ y, f y * far i (x-y)) := by
    funext x
    change (∫ y, f y * newtonGradientKernel i (x-y)) =
      (∫ y, near i y * f (x-y)) + ∫ y, f y * far i (x-y)
    rw [wji_convolution_swap (near i) f x, ← integral_add]
    · apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro y
      by_cases hz : x-y ∈ ball (0 : RSpace) 1
      · simp [near, far, hz]
      · simp [near, far, hz]
    · exact ((wji_newtonGradient_near_integrable i).comp_sub_left x).bdd_mul
        hf.aestronglyMeasurable (.of_forall hM)
    · exact hf1.mul_bdd ((far_meas i).comp (measurable_const.sub measurable_id)).aestronglyMeasurable
        (.of_forall (fun _ => far_le i _))
  rw [he]
  exact hn.add ht


theorem wji_transport_component_integrable (v w : WJISobolev.space) (i : Fin 3) :
    Integrable (fun x => transport v.val w.val x i) := by
  have ht (j : Fin 3) : Integrable
      (fun x => v.val x j * spatialDerivative j (fun y => w.val y i) x) :=
    memLp_one_iff_integrable.mp ((WJISobolev.memLp_partial w i j).mul' (WJISobolev.memLp_coord v j))
  exact ((ht 0).add (ht 1)).add (ht 2)

/-- The integration-by-parts expression for the Newton potential of a transport
divergence is always in L², even when the potential kernel itself is outside L². -/
theorem wji_transport_newton_parts_memL2 (v w : WJISobolev.space) :
    MemLp (fun x : RSpace => ∑ j : Fin 3, ∫ y,
      transport v.val w.val y j * newtonGradientKernel j (x-y)) 2 volume := by
  apply memLp_finsetSum
  intro j _
  have hj := WJISobolev.transport_mem v w j
  obtain ⟨M, hM⟩ := WJISobolev.scalar_bounded hj
  exact wji_newtonGradient_convolution_memL2 j (wji_transport_component_integrable v w j)
    (WJISobolev.scalar_memLp hj).1 (WJISobolev.scalar_smooth hj).continuous.measurable hM

/-- Each proposed component of the Newton gradient on the actual transport
source is square integrable. -/
theorem wji_transport_newton_gradient_memL2 (i : Fin 3) (v w : WJISobolev.space) :
    MemLp (fun x : RSpace => ∫ y, fieldDiv (transport v.val w.val) y *
      newtonGradientKernel i (x-y)) 2 volume := by
  have ht := WJISobolev.transport_mem v w
  have hD (j : Fin 3) := WJISobolev.scalar_partial (ht j) j
  have hsource : fieldDiv (transport v.val w.val) ∈ WJISobolev.scalar :=
    WJISobolev.scalar.add_mem (WJISobolev.scalar.add_mem (hD 0) (hD 1)) (hD 2)
  obtain ⟨M, hM⟩ := WJISobolev.transport_div_bounded v w
  exact wji_newtonGradient_convolution_memL2 i (WJISobolev.transport_div_integrable v w)
    (WJISobolev.scalar_memLp hsource).1 (WJISobolev.scalar_smooth hsource).continuous.measurable hM

theorem wji_newtonPotential_memL2_of_parts (v w : WJISobolev.space)
    (hparts : ∀ x, newtonPotential (fieldDiv (transport v.val w.val)) x =
      ∑ j : Fin 3, ∫ y, transport v.val w.val y j * newtonGradientKernel j (x-y)) :
    MemLp (newtonPotential (fieldDiv (transport v.val w.val))) 2 volume := by
  rw [funext hparts]
  exact wji_transport_newton_parts_memL2 v w

end
end CondFeffA
