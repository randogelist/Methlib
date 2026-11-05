import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

open Filter MeasureTheory Set
open scoped Topology

noncomputable section

namespace CondFeffB

private abbrev Space3 := Fin 3 → ℝ

private theorem cellSlice_integrable {K : Set Space3} {J : Set ℝ} {F : Space3 × ℝ → ℝ}
    (hK : IsCompact K) (hF : ContinuousOn F (K ×ˢ J)) {t : ℝ} (ht : t ∈ J) :
    IntegrableOn (fun x => F (x,t)) K volume := by
  have hc : ContinuousOn (fun x => F (x,t)) K :=
    hF.comp (Continuous.prodMk_left t).continuousOn (fun _ hx => ⟨hx, ht⟩)
  exact hc.integrableOn_compact hK

/-- Joint continuity on a compact space-time cylinder implies continuity of its spatial integral,
    including both time endpoints. -/
theorem cellIntegral_continuousOn_Icc {K : Set Space3} {a b : ℝ} {F : Space3 × ℝ → ℝ}
    (hK : IsCompact K) (hF : ContinuousOn F (K ×ˢ Icc a b)) :
    ContinuousOn (fun t => ∫ x in K, F (x,t)) (Icc a b) := by
  obtain ⟨B, hB⟩ := (hK.prod (isCompact_Icc : IsCompact (Icc a b))).exists_bound_of_continuousOn hF
  apply MeasureTheory.continuousOn_of_dominated (bound := fun _ : Space3 => B)
  · intro s hs
    exact (cellSlice_integrable hK hF hs).aestronglyMeasurable
  · intro s hs
    filter_upwards [ae_restrict_mem (μ := (volume : Measure Space3)) hK.measurableSet] with x hx
    exact hB (x,s) ⟨hx, hs⟩
  · exact (continuousOn_const : ContinuousOn (fun _ : Space3 => B) K).integrableOn_compact hK
  · filter_upwards [ae_restrict_mem (μ := (volume : Measure Space3)) hK.measurableSet] with x hx
    exact hF.comp (Continuous.prodMk_right x).continuousOn (fun _ ht => ⟨hx, ht⟩)

/-- At an interior time, integrate the pointwise time derivative; joint continuity on the
    cylinder supplies the compact integrable dominating constant. -/
theorem cellIntegral_hasDerivAt_Icc {K : Set Space3} {a t b : ℝ} {F G : Space3 × ℝ → ℝ}
    (hK : IsCompact K) (hat : a < t) (htb : t < b)
    (hF : ContinuousOn F (K ×ˢ Icc a b)) (hG : ContinuousOn G (K ×ˢ Icc a b))
    (hd : ∀ x ∈ K, ∀ s ∈ Icc a b, HasDerivAt (fun q => F (x,q)) (G (x,s)) s) :
    HasDerivAt (fun q => ∫ x in K, F (x,q)) (∫ x in K, G (x,t)) t := by
  obtain ⟨B, hB⟩ := (hK.prod (isCompact_Icc : IsCompact (Icc a b))).exists_bound_of_continuousOn hG
  have hN : Icc a b ∈ 𝓝 t := Icc_mem_nhds hat htb
  have ht : t ∈ Icc a b := ⟨hat.le, htb.le⟩
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := (volume : Measure Space3).restrict K)
    (F := fun s x => F (x,s)) (F' := fun s x => G (x,s)) (bound := fun _ => B)
    hN ?_ (cellSlice_integrable hK hF ht) (cellSlice_integrable hK hG ht).aestronglyMeasurable
    ?_ ?_ ?_).2
  · filter_upwards [hN] with s hs
    exact (cellSlice_integrable hK hF hs).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem (μ := (volume : Measure Space3)) hK.measurableSet] with x hx
    exact fun s hs => hB (x,s) ⟨hx, hs⟩
  · exact (continuousOn_const : ContinuousOn (fun _ : Space3 => B) K).integrableOn_compact hK
  · filter_upwards [ae_restrict_mem (μ := (volume : Measure Space3)) hK.measurableSet] with x hx
    exact hd x hx

/-- The integral is right-continuous at the initial time, and continuous throughout `Ici 0`. -/
theorem cellIntegral_continuousOn_Ici {K : Set Space3} {F : Space3 × ℝ → ℝ}
    (hK : IsCompact K) (hF : ContinuousOn F (K ×ˢ Ici 0)) :
    ContinuousOn (fun t => ∫ x in K, F (x,t)) (Ici 0) := by
  intro t ht
  have hsub : K ×ˢ Icc 0 (t+1) ⊆ K ×ˢ Ici 0 := fun _ h => ⟨h.1, h.2.1⟩
  have htc : t ∈ Icc 0 (t+1) := ⟨ht, by linarith⟩
  apply (cellIntegral_continuousOn_Icc hK (hF.mono hsub) t htc).mono_of_mem_nhdsWithin
  have hlt : t < t+1 := by linarith
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hlt)] with s hs hst
  exact ⟨hs, le_of_lt hst⟩

/-- A compact positive-time neighborhood suffices; no time differentiability at zero is used. -/
theorem cellIntegral_hasDerivAt_pos {K : Set Space3} {F G : Space3 × ℝ → ℝ}
    (hK : IsCompact K) (hF : ContinuousOn F (K ×ˢ Ici 0)) (hG : ContinuousOn G (K ×ˢ Ioi 0))
    (hd : ∀ x ∈ K, ∀ s > 0, HasDerivAt (fun q => F (x,q)) (G (x,s)) s)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => ∫ x in K, F (x,s)) (∫ x in K, G (x,t)) t := by
  have hp : ∀ s ∈ Icc (t/2) (t+1), 0 < s := fun s hs => lt_of_lt_of_le (by linarith) hs.1
  refine cellIntegral_hasDerivAt_Icc (a := t/2) (b := t+1) hK (by linarith) (by linarith) ?_ ?_ ?_
  · exact hF.mono (fun z hz => ⟨hz.1, (hp z.2 hz.2).le⟩)
  · exact hG.mono (fun z hz => ⟨hz.1, hp z.2 hz.2⟩)
  · exact fun x hx s hs => hd x hx s (hp s hs)

end CondFeffB
