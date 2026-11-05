import CondRecurrence
import Mathlib.MeasureTheory.Function.LpSpace.Complete

namespace CondFeffA

open Fefferman.ConcreteReal MeasureTheory Filter Set
open scoped Topology
noncomputable section

/-- Fatou's bound in Lᵖ, including p = ∞. The uniform slice bound is a
    finite ENNReal; convergence of the scalar fields is only pointwise. -/
theorem wji_scalar_memLp_of_positive_trace {p : ENNReal} {u : ℕ → RSpace → ℝ}
    {f : RSpace → ℝ} {C : ENNReal} (hC : C < ⊤)
    (hu : ∀ m, AEStronglyMeasurable (u m) volume)
    (hbound : ∀ m, eLpNorm (u m) p volume ≤ C)
    (htrace : ∀ x, Tendsto (fun m => u m x) atTop (𝓝 (f x))) :
    MemLp f p volume := by
  have he : ∀ᵐ x : RSpace, Tendsto (fun m => u m x) atTop (𝓝 (f x)) :=
    Filter.Eventually.of_forall htrace
  exact ⟨aestronglyMeasurable_of_tendsto_ae atTop hu he,
    (Lp.eLpNorm_le_of_ae_tendsto (Filter.Eventually.of_forall hbound) hu he).trans_lt hC⟩

theorem wji_trace_memLp_two_top {u : ℕ → RSpace → ℝ} {f : RSpace → ℝ}
    {C₂ Ctop : ENNReal} (hc₂ : C₂ < ⊤) (hctop : Ctop < ⊤)
    (hu : ∀ m, AEStronglyMeasurable (u m) volume)
    (hb₂ : ∀ m, eLpNorm (u m) 2 volume ≤ C₂)
    (hbtop : ∀ m, eLpNorm (u m) ⊤ volume ≤ Ctop)
    (htrace : ∀ x, Tendsto (fun m => u m x) atTop (𝓝 (f x))) :
    MemLp f 2 volume ∧ MemLp f ⊤ volume :=
  ⟨wji_scalar_memLp_of_positive_trace hc₂ hu hb₂ htrace,
   wji_scalar_memLp_of_positive_trace hctop hu hbtop htrace⟩


/-- Select times from a full-measure subset of a positive slab. They
    approach its initial face from the right. -/
theorem wji_good_times_tendsto_zero {T : ℝ} (hT : 0 < T) (A : ℝ → Prop)
    (ha : ∀ᵐ t : ℝ, t ∈ Ioo 0 T → A t) :
    ∃ r : ℕ → ℝ, (∀ m, r m ∈ Ioo 0 T ∧ A (r m)) ∧ Tendsto r atTop (𝓝 0) := by
  classical
  let ε (m : ℕ) : ℝ := min T (1 / ((m : ℝ) + 1))
  have pick (m : ℕ) : ∃ t ∈ Ioo 0 (ε m), A t := by
    have pos : 0 < ε m := lt_min hT (by positivity)
    have hvol : volume (Ioo 0 (ε m)) ≠ 0 := by
      rw [Real.volume_Ioo, sub_zero]
      exact ne_of_gt (ENNReal.ofReal_pos.mpr pos)
    have hfreq : ∃ᵐ t : ℝ, t ∈ Ioo 0 (ε m) := frequently_ae_mem_iff.mpr hvol
    obtain ⟨t, ht, hgood⟩ := (hfreq.and_eventually ha).exists
    exact ⟨t, ht, hgood ⟨ht.1, ht.2.trans_le (min_le_left _ _)⟩⟩
  choose r hr hgood using pick
  refine ⟨r, fun m => ⟨⟨(hr m).1, (hr m).2.trans_le (min_le_left _ _)⟩, hgood m⟩, ?_⟩
  exact squeeze_zero (fun m => (hr m).1.le)
    (fun m => (hr m).2.le.trans (min_le_right _ _))
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

/-- Essential-in-time slice bounds pass to the initial trace. This needs
    only continuity at zero in time for each spatial point. -/
theorem wji_trace_memLp_two_top_of_ae_slab {T : ℝ} (hT : 0 < T)
    (u : ℝ → RSpace → ℝ) {C₂ Ctop : ENNReal} (hc₂ : C₂ < ⊤) (hctop : Ctop < ⊤)
    (hcont : ∀ x, ContinuousWithinAt (fun t => u t x) (Ici 0) 0)
    (hslab : ∀ᵐ t : ℝ, t ∈ Ioo 0 T →
      AEStronglyMeasurable (u t) volume ∧
      eLpNorm (u t) 2 volume ≤ C₂ ∧ eLpNorm (u t) ⊤ volume ≤ Ctop) :
    MemLp (u 0) 2 volume ∧ MemLp (u 0) ⊤ volume := by
  obtain ⟨r, hr, hlim⟩ := wji_good_times_tendsto_zero hT _ hslab
  have hright : Tendsto r atTop (𝓝[Ici (0 : ℝ)] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hlim, Filter.Eventually.of_forall (fun m => (hr m).1.1.le)⟩
  exact wji_trace_memLp_two_top (u := fun m => u (r m)) hc₂ hctop
    (fun m => (hr m).2.1) (fun m => (hr m).2.2.1) (fun m => (hr m).2.2.2)
    (fun x => (hcont x).tendsto.comp hright)

end
end CondFeffA

#print axioms CondFeffA.wji_scalar_memLp_of_positive_trace
#print axioms CondFeffA.wji_trace_memLp_two_top
#print axioms CondFeffA.wji_good_times_tendsto_zero
#print axioms CondFeffA.wji_trace_memLp_two_top_of_ae_slab
