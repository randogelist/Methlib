import SingularClosure.CriticalSpacesCutoff
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Analysis.InnerProductSpace.Basic

/-! Weak Hilbert continuity from continuous Fourier coordinates and a uniform
energy bound. Strong initial trace follows when that bound is the initial norm.
No compactness or PDE premise is replaced by an admission in these lemmas. -/
set_option autoImplicit false
set_option Elab.async true
open Set Filter
open scoped Topology BigOperators ENNReal
namespace QuasiFeffermanB
open SingularClosure
noncomputable section

theorem energy_lp_inner_projection (z w : FourierVectorSequence)
    (S : Finset FourierIndex) :
    inner ℂ z (criticalLpProjection S w) = ∑ ki ∈ S, inner ℂ (z ki) (w ki) := by
  classical
  rw [lp.inner_eq_tsum]
  rw [tsum_eq_sum (s := S) (fun ki hki => by
    simp only [criticalLpProjection_apply, if_neg hki, inner_zero_right])]
  apply Finset.sum_congr rfl
  intro ki hki
  simp only [criticalLpProjection_apply, if_pos hki]

theorem energy_lp_projection_tendsto (w : FourierVectorSequence) :
    Tendsto (fun S : Finset FourierIndex => criticalLpProjection S w)
      atTop (𝓝 w) := by
  have hsum : Tendsto
      (fun S : Finset FourierIndex => ∑ ki ∈ S, lp.single 2 ki (w ki))
      atTop (𝓝 w) := lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ∞) w
  simpa only [criticalLpProjection_eq_sum] using hsum

theorem ENERGY_LP_WEAK_CONTINUITY
    (U : ℝ → FourierVectorSequence) (I : Set ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hbound : ∀ t ∈ I, ‖U t‖ ≤ R)
    (hcoord : ∀ ki : FourierIndex, ContinuousOn (fun t => U t ki) I)
    (w : FourierVectorSequence) :
    ContinuousOn (fun t => inner ℂ (U t) w) I := by
  classical
  have hfinite : ∀ S : Finset FourierIndex,
      ContinuousOn (fun t => inner ℂ (U t) (criticalLpProjection S w)) I := by
    intro S
    simp_rw [energy_lp_inner_projection]
    apply continuousOn_finset_sum
    intro ki hki
    exact (hcoord ki).inner continuousOn_const
  have huniform : TendstoUniformlyOn
      (fun S : Finset FourierIndex => fun t => inner ℂ (U t) (criticalLpProjection S w))
      (fun t => inner ℂ (U t) w) atTop I := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hRp : 0 < R + 1 := by linarith
    filter_upwards [Metric.tendsto_nhds.mp (energy_lp_projection_tendsto w)
      (ε / (R + 1)) (div_pos hε hRp)] with S hS
    intro t ht
    rw [dist_comm]
    have htail : ‖criticalLpProjection S w - w‖ < ε / (R + 1) := by
      simpa only [dist_eq_norm] using hS
    calc
      dist (inner ℂ (U t) (criticalLpProjection S w)) (inner ℂ (U t) w)
          = ‖inner ℂ (U t) (criticalLpProjection S w - w)‖ := by
              rw [dist_eq_norm, inner_sub_right]
      _ ≤ ‖U t‖ * ‖criticalLpProjection S w - w‖ := norm_inner_le_norm _ _
      _ ≤ R * ‖criticalLpProjection S w - w‖ :=
        mul_le_mul_of_nonneg_right (hbound t ht) (norm_nonneg _)
      _ ≤ (R + 1) * ‖criticalLpProjection S w - w‖ :=
        mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
      _ < ε := by
        have h := (lt_div_iff₀ hRp).mp htail
        nlinarith
  exact huniform.continuousOn (Eventually.of_forall hfinite).frequently

theorem ENERGY_H0_WEAK_CONTINUITY
    (U : ℝ → TorusSobolev 0) (I : Set ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hbound : ∀ t ∈ I, ‖U t‖ ≤ R)
    (hcoord : ∀ k i, ContinuousOn (fun t => (U t).val k i) I)
    (w : TorusSobolev 0) :
    ContinuousOn (fun t => inner ℂ (U t) w) I := by
  have hb : ∀ t ∈ I, ‖torusSobolevRepr 0 (U t)‖ ≤ R := by
    intro t ht
    simpa only [(torusSobolevRepr 0).norm_map] using hbound t ht
  have hc : ∀ ki : FourierIndex,
      ContinuousOn (fun t => torusSobolevRepr 0 (U t) ki) I := by
    intro ki
    simpa only [torusSobolevRepr_apply, pow_zero, one_mul] using hcoord ki.1 ki.2
  have h := ENERGY_LP_WEAK_CONTINUITY
    (fun t => torusSobolevRepr 0 (U t)) I R hR hb hc (torusSobolevRepr 0 w)
  simpa only [(torusSobolevRepr 0).inner_map_map] using h

theorem energy_complex_strong_tendsto_of_inner_and_norm_bound
    {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {l : Filter ι} {f : ι → E} {a : E}
    (hinner : Tendsto (fun i => Complex.re (inner ℂ (f i) a)) l (𝓝 (‖a‖ ^ 2)))
    (hbound : ∀ᶠ i in l, ‖f i‖ ^ 2 ≤ ‖a‖ ^ 2) :
    Tendsto f l (𝓝 a) := by
  have hupper : Tendsto
      (fun i => 2 * ‖a‖ ^ 2 - 2 * Complex.re (inner ℂ (f i) a)) l (𝓝 0) := by
    have hc : Tendsto (fun _ : ι => 2 * ‖a‖ ^ 2) l (𝓝 (2 * ‖a‖ ^ 2)) :=
      tendsto_const_nhds
    have ht : Tendsto (fun i => 2 * Complex.re (inner ℂ (f i) a))
        l (𝓝 (2 * ‖a‖ ^ 2)) := tendsto_const_nhds.mul hinner
    simpa only [sub_self] using hc.sub ht
  have hsquare : Tendsto (fun i => ‖f i - a‖ ^ 2) l (𝓝 (0 : ℝ)) := by
    apply squeeze_zero' (Eventually.of_forall (fun i => sq_nonneg ‖f i - a‖))
      ?_ hupper
    filter_upwards [hbound] with i hi
    rw [norm_sub_sq (𝕜 := ℂ)]
    change ‖f i‖ ^ 2 - 2 * Complex.re (inner ℂ (f i) a) + ‖a‖ ^ 2 ≤
      2 * ‖a‖ ^ 2 - 2 * Complex.re (inner ℂ (f i) a)
    linarith
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hsquare
  have hn : Tendsto (fun i => ‖f i - a‖) l (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero]
      using hsqrt
  apply tendsto_iff_dist_tendsto_zero.mpr
  simpa only [dist_eq_norm] using hn

theorem ENERGY_H0_STRONG_INITIAL_TRACE
    (U : ℝ → TorusSobolev 0)
    (hbound : ∀ t ∈ Ici (0 : ℝ), ‖U t‖ ≤ ‖U 0‖)
    (hcoord : ∀ k i, ContinuousOn (fun t => (U t).val k i) (Ici 0)) :
    Tendsto U (𝓝[Ici 0] 0) (𝓝 (U 0)) := by
  have hw := ENERGY_H0_WEAK_CONTINUITY U (Ici 0) ‖U 0‖
    (norm_nonneg _) hbound hcoord (U 0)
  have hi : Tendsto (fun t => Complex.re (inner ℂ (U t) (U 0)))
      (𝓝[Ici 0] 0) (𝓝 (‖U 0‖ ^ 2)) := by
    have h := Complex.continuous_re.continuousAt.tendsto.comp (hw 0 (by simp))
    have hself : Complex.re (inner ℂ (U 0) (U 0)) = ‖U 0‖ ^ 2 :=
      inner_self_eq_norm_sq (𝕜 := ℂ) (U 0)
    simpa only [Function.comp_def, hself] using h
  apply energy_complex_strong_tendsto_of_inner_and_norm_bound hi
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact pow_le_pow_left₀ (norm_nonneg _) (hbound t ht) 2

end
end QuasiFeffermanB
