import WJIHarmonicPressure
import WJITraceBounds

namespace CondFeffA
open Fefferman Fefferman.ConcreteReal WJISmooth MeasureTheory Filter Set
open scoped ContDiff Topology
noncomputable section

/-- Read a spatial derivative word from left to right. The empty word is the field itself. -/
def wjiSpatialWord : List (Fin 3) → (RSpace → ℝ) → RSpace → ℝ
  | [], f => f
  | i :: is, f => wjiSpatialWord is (spatialDerivative i f)

private def slabWord : List (Fin 3) → ((RSpace × ℝ) → ℝ) → (RSpace × ℝ) → ℝ
  | [], F => F
  | i :: is, F => slabWord is (fun z => spatialDerivative i (fun y => F (y,z.2)) z.1)

private theorem slabWord_slice (w : List (Fin 3)) (F : (RSpace × ℝ) → ℝ) (t : ℝ) :
    (fun y => slabWord w F (y,t)) = wjiSpatialWord w (fun y => F (y,t)) := by
  induction w generalizing F with
  | nil => rfl
  | cons i is ih => exact ih (fun z => spatialDerivative i (fun y => F (y,z.2)) z.1)

private theorem slabWord_smooth (w : List (Fin 3)) {F : (RSpace × ℝ) → ℝ}
    (hF : ContDiffOn ℝ ⊤ F {z | 0 ≤ z.2}) :
    ContDiffOn ℝ ⊤ (slabWord w F) {z | 0 ≤ z.2} := by
  induction w generalizing F with
  | nil => exact hF
  | cons i is ih => exact ih (spatialSlice_smooth hF i)

/-- The differentiated positive-time velocity. No initial-face derivative occurs here. -/
def wjiPositiveTimeWord (s : Solution realAnalysis) (n : ℕ) (i : Fin 3)
    (w : List (Fin 3)) (t : ℝ) : RSpace → ℝ :=
  wjiSpatialWord w (fun y => iteratedDeriv n (fun r => s.velocity y r i) t)

/-- Local a.e.-in-time Sobolev bounds for classical mixed derivatives. One positive
horizon and finite constants per word and component suffice. -/
def WJIPositiveTimeWordBounds (δ : ℝ) : Prop :=
  ∀ c ∈ Ioo 0 δ, ∀ s : Solution realAnalysis, IsWitness c s →
    ∀ (n : ℕ) (i : Fin 3) (w : List (Fin 3)),
    ∃ T : ℝ, 0 < T ∧ ∃ C₂ Ctop : ENNReal, C₂ < ⊤ ∧ Ctop < ⊤ ∧
      ∀ᵐ t : ℝ, t ∈ Ioo 0 T →
        eLpNorm (wjiPositiveTimeWord s n i w t) 2 volume ≤ C₂ ∧
        eLpNorm (wjiPositiveTimeWord s n i w t) ⊤ volume ≤ Ctop

private theorem smooth_word_order (n : ℕ) (g : scalarSpace)
    (hg : ∀ w, MemLp (wjiSpatialWord w g.val) 2 volume ∧ MemLp (wjiSpatialWord w g.val) ⊤ volume) :
    g ∈ WJISobolev.order n := by
  induction n generalizing g with
  | zero => exact hg []
  | succ n ih =>
    simp only [WJISobolev.order, Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap]
    exact ⟨ih g hg, fun i => ih (partialMap i g) (fun w => hg (i :: w))⟩

theorem wji_scalar_sobolev_of_word_bounds {g : RSpace → ℝ} (hs : ContDiff ℝ ∞ g)
    (hg : ∀ w, MemLp (wjiSpatialWord w g) 2 volume ∧ MemLp (wjiSpatialWord w g) ⊤ volume) :
    g ∈ WJISobolev.scalar := by
  change g ∈ (⨅ n : ℕ, WJISobolev.order n).map scalarSpace.subtype
  apply Submodule.mem_map.mpr
  refine ⟨⟨g, hs⟩, (Submodule.mem_iInf _).mpr ?_, rfl⟩
  exact fun n => smooth_word_order n ⟨g,hs⟩ hg

/-- Each closed-face spatial time jet inherits the L² and L∞ bounds on its
classical positive-time mixed derivatives by pointwise convergence and Fatou. -/
theorem wji_jetsInSobolevSpace_of_positive_time_word_bounds {δ : ℝ}
    (hb : WJIPositiveTimeWordBounds δ) : WJIJetsInSobolevSpace δ := by
  intro c hc s hs n i
  apply wji_scalar_sobolev_of_word_bounds ((wji_velocityJet_analytic hs n i).of_le le_top)
  intro w
  obtain ⟨T, hT, C₂, Ctop, hc₂, hctop, habt⟩ := hb c hc s hs n i w
  let F : RSpace × ℝ → ℝ := fun z => s.velocity z.1 z.2 i
  let J : RSpace × ℝ → ℝ := fun z => iteratedDerivWithin n (fun t => F (z.1,t)) (Ici 0) z.2
  have hF : ContDiffOn ℝ ⊤ F {z | 0 ≤ z.2} := hs.2.2.2.1.1 i
  have hG := slabWord_smooth w (wji_spacetime_analytic_timeJet hF n)
  let U (t : ℝ) (x : RSpace) := slabWord w J (x,t)
  have hsame (t : ℝ) (ht : 0 < t) : U t = wjiPositiveTimeWord s n i w t := by
    have hone : (fun y => J (y,t)) = fun y => iteratedDeriv n (fun r => s.velocity y r i) t := by
      funext y
      have hh : ContDiffAt ℝ (n : ℕ∞ω) (fun r => F (y,r)) t :=
        ((slicing hF y).contDiffAt (Ici_mem_nhds ht)).of_le le_top
      exact iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ici 0) hh (ht.le)
    exact (slabWord_slice w J t).trans (congrArg (wjiSpatialWord w) hone)
  have hface : U 0 = wjiSpatialWord w (fun y => timeJetField s n y i) :=
    slabWord_slice w J 0
  rw [← hface]
  apply wji_trace_memLp_two_top_of_ae_slab hT U hc₂ hctop
  · intro x
    exact (slicing hG x).continuousOn 0 Set.self_mem_Ici
  · filter_upwards [habt] with t ht
    intro hI
    have f : ContDiff ℝ ⊤ (fun y : RSpace => slabWord w J (y,t)) :=
      hG.comp_contDiff (f := fun y : RSpace => (y,t))
        (contDiff_id.prodMk contDiff_const) (fun _ => hI.1.le)
    refine ⟨f.continuous.aestronglyMeasurable, ?_⟩
    rw [hsame t hI.1]
    exact ht hI

end
end CondFeffA
