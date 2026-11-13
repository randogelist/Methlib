import Mathlib

/-!
QFA extraction: D09.04; indexed existing sources EP096.
Status: A_TIER_CANDIDATE. External compiler and axiom audit pending.
Origin: randogelist/Methlib@8a30134611027f99f4855c062f7903069cdca8d8
regularity-B-assembly/Singular-Axiomatic-closure/SingularClosure/CriticalUniqueness.lean
Transformation: namespace substitution only; original proof bodies retained.
Physical whole-space testing and common trace remain explicit hypotheses.
No root QFA theorem is declared by this scalar module.
-/


/-!
Scalar relative-energy comparison with admissible initial times.

The energy itself need not be continuous or differentiable.  Two integral
primitives reduce its Volterra inequality to a classical integrating factor.
The final theorem takes the admissible times to zero using the strong trace.
No weak NSE testing identity or PDE uniqueness theorem is assumed here.
-/

set_option autoImplicit false
set_option Elab.async true

noncomputable section

open Set MeasureTheory Filter
open scoped Interval Topology

namespace QFA.Endpoints.Comparison

private theorem critical_comparison_primitive_continuous
    {f : ℝ → ℝ} {s T : ℝ} (hst : s ≤ T)
    (hf : IntervalIntegrable f volume s T) :
    ContinuousOn (fun t : ℝ => ∫ r in s..t, f r) (Icc s T) := by
  simpa only [uIcc_of_le hst] using
    (intervalIntegral.continuousOn_primitive_interval' hf
      (left_mem_uIcc : s ∈ uIcc s T))

private theorem critical_comparison_primitive_hasDerivAt
    {f : ℝ → ℝ} {s T t : ℝ}
    (hf : ContinuousOn f (Icc s T)) (ht : t ∈ Ioo s T) :
    HasDerivAt (fun x : ℝ => ∫ r in s..x, f r) (f t) t := by
  have hi : IntervalIntegrable f volume s t :=
    (hf.mono (Icc_subset_Icc le_rfl ht.2.le)).intervalIntegrable_of_Icc ht.1.le
  have hm : StronglyMeasurableAtFilter f (nhds t) volume :=
    ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo
      (hf.mono Ioo_subset_Icc_self) t ht
  exact intervalIntegral.integral_hasDerivAt_right hi hm
    (hf.continuousAt (Icc_mem_nhds ht.1 ht.2))

/-- Differential Gronwall on an arbitrary closed interval; endpoint
 derivatives and the sign of the coefficient are not required. -/
theorem critical_comparison_differential_gronwall
    {y d a : ℝ → ℝ} {s T : ℝ} (hst : s ≤ T)
    (hy : ContinuousOn y (Icc s T)) (ha : ContinuousOn a (Icc s T))
    (hderiv : ∀ t ∈ Ioo s T, HasDerivAt y (d t) t)
    (hbound : ∀ t ∈ Ioo s T, d t ≤ a t * y t) :
    ∀ t ∈ Icc s T, y t ≤ y s * Real.exp (∫ r in s..t, a r) := by
  let A : ℝ → ℝ := fun t => ∫ r in s..t, a r
  let F : ℝ → ℝ := fun t => y t * Real.exp (-A t)
  have hAc : ContinuousOn A (Icc s T) :=
    critical_comparison_primitive_continuous hst (ha.intervalIntegrable_of_Icc hst)
  have hFc : ContinuousOn F (Icc s T) :=
    hy.mul (Real.continuous_exp.comp_continuousOn hAc.neg)
  have hFd : ∀ t ∈ Ioo s T,
      HasDerivAt F ((d t - a t * y t) * Real.exp (-A t)) t := by
    intro t ht
    have hAd : HasDerivAt A (a t) t :=
      critical_comparison_primitive_hasDerivAt ha ht
    have hraw : HasDerivAt F
        (d t * Real.exp (-A t) + y t * (Real.exp (-A t) * (-a t))) t :=
      (hderiv t ht).mul hAd.neg.exp
    convert hraw using 1 <;> ring
  have hanti : AntitoneOn F (Icc s T) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc s T) hFc
    · intro t ht
      have ht' : t ∈ Ioo s T := by simpa only [interior_Icc] using ht
      exact (hFd t ht').differentiableAt.differentiableWithinAt
    · intro t ht
      have ht' : t ∈ Ioo s T := by simpa only [interior_Icc] using ht
      rw [(hFd t ht').deriv]
      exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hbound t ht'))
        (Real.exp_pos _).le
  intro t ht
  have hfactor : y t * Real.exp (-A t) ≤ y s := by
    have h := hanti ⟨le_rfl, hst⟩ ht ht.1
    simpa only [F, A, intervalIntegral.integral_same, neg_zero,
      Real.exp_zero, mul_one] using h
  have hcancel : Real.exp (-A t) * Real.exp (A t) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  calc
    y t = (y t * Real.exp (-A t)) * Real.exp (A t) := by
      rw [mul_assoc, hcancel, mul_one]
    _ ≤ y s * Real.exp (A t) :=
      mul_le_mul_of_nonneg_right hfactor (Real.exp_pos _).le

/-- Integral Gronwall for a possibly discontinuous relative energy.
 Only the product `a * e` must be integrable. -/
theorem CRITICAL_RELATIVE_ENERGY_GRONWALL
    {e a : ℝ → ℝ} {s T δ : ℝ} (hst : s ≤ T)
    (ha : ContinuousOn a (Icc s T))
    (ha_nonneg : ∀ t ∈ Icc s T, 0 ≤ a t)
    (hprod : IntervalIntegrable (fun r => a r * e r) volume s T)
    (hrelative : ∀ t ∈ Icc s T,
      e t ≤ δ + ∫ r in s..t, a r * e r) :
    ∀ t ∈ Icc s T, e t ≤ δ * Real.exp (∫ r in s..t, a r) := by
  let F : ℝ → ℝ := fun t => δ + ∫ r in s..t, a r * e r
  let G : ℝ → ℝ := fun t => δ + ∫ r in s..t, a r * F r
  have hF : ContinuousOn F (Icc s T) :=
    continuousOn_const.add (critical_comparison_primitive_continuous hst hprod)
  have haF : ContinuousOn (fun r => a r * F r) (Icc s T) := ha.mul hF
  have hG : ContinuousOn G (Icc s T) :=
    continuousOn_const.add (critical_comparison_primitive_continuous hst
      (haF.intervalIntegrable_of_Icc hst))
  have heF : ∀ t ∈ Icc s T, e t ≤ F t := hrelative
  have hFG : ∀ t ∈ Icc s T, F t ≤ G t := by
    intro t ht
    have hp : IntervalIntegrable (fun r => a r * e r) volume s t := by
      apply hprod.mono_set
      rw [uIcc_of_le ht.1, uIcc_of_le hst]
      exact Icc_subset_Icc le_rfl ht.2
    have hq : IntervalIntegrable (fun r => a r * F r) volume s t :=
      (haF.mono (Icc_subset_Icc le_rfl ht.2)).intervalIntegrable_of_Icc ht.1
    change δ + (∫ r in s..t, a r * e r) ≤ δ + (∫ r in s..t, a r * F r)
    apply add_le_add le_rfl
    apply intervalIntegral.integral_mono_on ht.1 hp hq
    intro r hr
    have hrT : r ∈ Icc s T := ⟨hr.1, hr.2.trans ht.2⟩
    exact mul_le_mul_of_nonneg_left (heF r hrT) (ha_nonneg r hrT)
  have hGd : ∀ t ∈ Ioo s T, HasDerivAt G (a t * F t) t := by
    intro t ht
    exact (critical_comparison_primitive_hasDerivAt haF ht).const_add δ
  have hGbound : ∀ t ∈ Ioo s T, a t * F t ≤ a t * G t := by
    intro t ht
    exact mul_le_mul_of_nonneg_left (hFG t ⟨ht.1.le, ht.2.le⟩)
      (ha_nonneg t ⟨ht.1.le, ht.2.le⟩)
  have hgronwall := critical_comparison_differential_gronwall hst hG ha hGd hGbound
  intro t ht
  calc
    e t ≤ F t := heF t ht
    _ ≤ G t := hFG t ht
    _ ≤ G s * Real.exp (∫ r in s..t, a r) := hgronwall t ht
    _ = δ * Real.exp (∫ r in s..t, a r) := by
      simp only [G, intervalIntegral.integral_same, add_zero]

/-- Admissible positive initial times may tend to zero.  A strong common
 trace then eliminates the relative energy on the entire positive interval.

This scalar theorem does not supply the PDE cross-testing inequality: that
 inequality is precisely `hrelative`, retained as an explicit hypothesis. -/
theorem CRITICAL_RELATIVE_ENERGY_ZERO_OF_ADMISSIBLE_TRACE
    {e a : ℝ → ℝ} {T M : ℝ} {ε : ℕ → ℝ}
    (hT : 0 < T)
    (he_nonneg : ∀ t ∈ Icc 0 T, 0 ≤ e t)
    (ha : ContinuousOn a (Ioc 0 T))
    (ha_nonneg : ∀ t ∈ Ioc 0 T, 0 ≤ a t)
    (ha_integrable : IntervalIntegrable a volume 0 T)
    (hprod : IntervalIntegrable (fun r => a r * e r) volume 0 T)
    (hbudget : (∫ r in (0 : ℝ)..T, a r) ≤ M)
    (hε : ∀ n, ε n ∈ Ioc 0 T)
    (hε_zero : Tendsto ε atTop (𝓝 0))
    (htrace : Tendsto (fun n => e (ε n)) atTop (𝓝 0))
    (hrelative : ∀ n t, t ∈ Icc (ε n) T →
      e t ≤ e (ε n) + ∫ r in ε n..t, a r * e r) :
    ∀ t ∈ Ioc 0 T, e t = 0 := by
  intro t ht
  have hevent : ∀ᶠ n : ℕ in atTop, ε n < t :=
    hε_zero.eventually (Iio_mem_nhds ht.1)
  have hbound : ∀ᶠ n : ℕ in atTop, e t ≤ e (ε n) * Real.exp M := by
    filter_upwards [hevent] with n hnt
    have hsubset : Icc (ε n) T ⊆ Ioc 0 T := by
      intro r hr
      exact ⟨lt_of_lt_of_le (hε n).1 hr.1, hr.2⟩
    have hpn : IntervalIntegrable (fun r => a r * e r) volume (ε n) T := by
      apply hprod.mono_set
      rw [uIcc_of_le (hε n).2, uIcc_of_le hT.le]
      exact Icc_subset_Icc (hε n).1.le le_rfl
    have hlocal := CRITICAL_RELATIVE_ENERGY_GRONWALL (hε n).2
      (ha.mono hsubset) (fun r hr => ha_nonneg r (hsubset hr)) hpn (hrelative n)
    have hA : (∫ r in ε n..t, a r) ≤ M := by
      apply le_trans _ hbudget
      apply intervalIntegral.integral_mono_interval (hε n).1.le hnt.le ht.2
        _ ha_integrable
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      exact ha_nonneg r hr
    exact (hlocal t ⟨hnt.le, ht.2⟩).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hA)
        (he_nonneg (ε n) ⟨(hε n).1.le, (hε n).2⟩))
  have hlim : Tendsto (fun n => e (ε n) * Real.exp M) atTop (𝓝 0) := by
    simpa only [zero_mul] using htrace.mul_const (Real.exp M)
  exact le_antisymm (ge_of_tendsto hlim hbound) (he_nonneg t ⟨ht.1.le, ht.2⟩)

-- D09.04 / EP096: every source premise is retained in the endpoint signature.
/-- Norm-valued comparison: two strong traces at the same datum supply the
vanishing relative-energy trace required by the scalar theorem. -/
theorem CRITICAL_COMPARISON_EQ_OF_ADMISSIBLE_TRACE
    {V : Type*} [NormedAddCommGroup V]
    {u v : ℝ → V} {a : ℝ → ℝ} {a₀ : V} {T M : ℝ} {ε : ℕ → ℝ}
    (hT : 0 < T)
    (ha : ContinuousOn a (Ioc 0 T))
    (ha_nonneg : ∀ t ∈ Ioc 0 T, 0 ≤ a t)
    (ha_integrable : IntervalIntegrable a volume 0 T)
    (hprod : IntervalIntegrable (fun r => a r * ‖u r - v r‖ ^ 2) volume 0 T)
    (hbudget : (∫ r in (0 : ℝ)..T, a r) ≤ M)
    (hε : ∀ n, ε n ∈ Ioc 0 T)
    (hε_zero : Tendsto ε atTop (𝓝 0))
    (hu_trace : Tendsto (fun n => u (ε n)) atTop (𝓝 a₀))
    (hv_trace : Tendsto (fun n => v (ε n)) atTop (𝓝 a₀))
    (hrelative : ∀ n t, t ∈ Icc (ε n) T →
      ‖u t - v t‖ ^ 2 ≤ ‖u (ε n) - v (ε n)‖ ^ 2 +
        ∫ r in ε n..t, a r * ‖u r - v r‖ ^ 2) :
    ∀ t ∈ Ioc 0 T, u t = v t := by
  have htrace : Tendsto (fun n => ‖u (ε n) - v (ε n)‖ ^ 2) atTop (𝓝 0) := by
    simpa using (hu_trace.sub hv_trace).norm.pow 2
  have hzero := CRITICAL_RELATIVE_ENERGY_ZERO_OF_ADMISSIBLE_TRACE hT
    (fun t _ => sq_nonneg ‖u t - v t‖) ha ha_nonneg ha_integrable hprod hbudget
    hε hε_zero htrace hrelative
  intro t ht
  have hn : ‖u t - v t‖ = 0 := by
    nlinarith only [hzero t ht, norm_nonneg (u t - v t)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

end QFA.Endpoints.Comparison

