import CondPressure

namespace CondFeffA

open Fefferman Fefferman.ConcreteReal Set Filter
open scoped Topology
noncomputable section

private abbrev Z := RSpace × ℝ
private def Q : Set Z := {z | 0 ≤ z.2}

private lemma uq : UniqueDiffOn ℝ Q := by
  have h : Q = (Set.univ : Set RSpace) ×ˢ Set.Ici (0 : ℝ) := by
    ext z
    simp [Q]
  rw [h]
  exact uniqueDiffOn_univ.prod (uniqueDiffOn_Ici 0)

private def Xd (i : Fin 3) (F : Z → ℝ) (z : Z) : ℝ :=
  spatialDerivative i (fun y => F (y,z.2)) z.1

theorem raw_space_deriv_within_eq {F : Z → ℝ} (hF : ContDiffOn ℝ ⊤ F Q)
    (i : Fin 3) (z : Z) (hz : z ∈ Q) :
    Xd i F z = (fderivWithin ℝ F Q z) (basisDirection i, 0) := by
  have hs := (hF.differentiableOn (by simp) z hz).hasFDerivWithinAt
  let emb : RSpace → Z := fun y => (y, z.2)
  have he : HasFDerivAt emb ((ContinuousLinearMap.id ℝ RSpace).prod 0) z.1 :=
    (hasFDerivAt_id z.1).prodMk (hasFDerivAt_const z.2 z.1)
  have hem : ∀ᶠ y in 𝓝 z.1, emb y ∈ Q := .of_forall fun _ => hz
  have hcomp := hs.comp_hasFDerivAt (f := emb) z.1 he hem
  change (fderiv ℝ (F ∘ emb) z.1) (basisDirection i) = _
  rw [hcomp.fderiv] <;> rfl

theorem spatialSlice_smooth {F : RSpace × ℝ → ℝ}
    (hF : ContDiffOn ℝ ⊤ F {z | 0 ≤ z.2}) (i : Fin 3) :
    ContDiffOn ℝ ⊤ (fun z : RSpace × ℝ => spatialDerivative i (fun y => F (y,z.2)) z.1)
      {z | 0 ≤ z.2} := by
  have hdf : ContDiffOn ℝ ⊤ (fderivWithin ℝ F Q) Q := hF.fderivWithin uq le_top
  let v : Z := (basisDirection i, 0)
  apply (hdf.clm_apply (g := fun _ => v) contDiffOn_const).congr
  exact raw_space_deriv_within_eq hF i

theorem raw_uniqueDiffOn : UniqueDiffOn ℝ {z : RSpace × ℝ | 0 ≤ z.2} := uq

theorem slicing {F : Z → ℝ} (hf : ContDiffOn ℝ ⊤ F Q) (x : RSpace) :
    ContDiffOn ℝ ⊤ (fun t : ℝ => F (x,t)) (Ici 0) :=
  hf.comp ((contDiff_const.prodMk contDiff_id).contDiffOn) (fun _ ht => ht)

def rawRHS (s : Solution realAnalysis) (x : RSpace) (i : Fin 3) (t : ℝ) : ℝ :=
  heatStep (fun y => s.velocity y t) x i -
    transport (fun y => s.velocity y t) (fun y => s.velocity y t) x i -
    spatialDerivative i (fun y => s.pressure y t) x

private theorem raw_smooth {c : ℝ} {s : Solution realAnalysis} (hs : IsWitness c s)
    (x : RSpace) (i : Fin 3) : ContDiffOn ℝ ⊤ (rawRHS s x i) (Ici 0) := by
  let u (j : Fin 3) : Z → ℝ := fun z => s.velocity z.1 z.2 j
  let p : Z → ℝ := fun z => s.pressure z.1 z.2
  have h6 : clause06 realAnalysis s := hs.2.2.2.1
  have hu (j : Fin 3) : ContDiffOn ℝ ⊤ (u j) Q := h6.1 j
  have hp : ContDiffOn ℝ ⊤ p Q := h6.2
  have hh (j : Fin 3) := spatialSlice_smooth (spatialSlice_smooth (hu i) j) j
  have ht (j : Fin 3) := (hu j).mul (spatialSlice_smooth (hu i) j)
  exact slicing (((((hh 0).add (hh 1)).add (hh 2)).sub
    (((ht 0).add (ht 1)).add (ht 2))).sub (spatialSlice_smooth hp i)) x

/-- The ambient derivative at t=0 need not equal the right derivative by
definition. The positive-time PDE and closed-half-space smoothness imply the
right-hand PDE there by continuity. -/
theorem raw_time_jet {c : ℝ} {s : Solution realAnalysis} (hs : IsWitness c s)
    (n : ℕ) (x : RSpace) (i : Fin 3) :
    timeJetField s (n+1) x i = rightJet (rawRHS s x i) n := by
  let u : ℝ → ℝ := fun t => s.velocity x t i
  have h6 : clause06 realAnalysis s := hs.2.2.2.1
  have hu : ContDiffOn ℝ ⊤ u (Ici 0) := slicing (h6.1 i) x
  have hdu : ContDiffOn ℝ ⊤ (derivWithin u (Ici 0)) (Ici 0) :=
    hu.derivWithin (uniqueDiffOn_Ici 0) le_top
  have hpos : EqOn (derivWithin u (Ici 0)) (rawRHS s x i) (Ioi 0) := by
    intro t ht
    rw [derivWithin_of_mem_nhds (Ici_mem_nhds ht)]
    have hm := hs.1 x t (le_of_lt ht) i
    change deriv u t + transport (fun y => s.velocity y t) (fun y => s.velocity y t) x i =
      1 * heatStep (fun y => s.velocity y t) x i +
        (-spatialDerivative i (fun y => s.pressure y t) x) + 0 at hm
    unfold rawRHS
    linarith
  have hall : EqOn (derivWithin u (Ici 0)) (rawRHS s x i) (Ici 0) :=
    hpos.of_subset_closure hdu.continuousOn (raw_smooth hs x i).continuousOn
      Ioi_subset_Ici_self (by rw [closure_Ioi])
  change iteratedDerivWithin (n+1) u (Ici 0) 0 =
    iteratedDerivWithin n (rawRHS s x i) (Ici 0) 0
  rw [iteratedDerivWithin_succ']
  exact iteratedDerivWithin_congr hall (Set.self_mem_Ici : (0 : ℝ) ∈ Set.Ici 0)

theorem raw_first_jet {c : ℝ} {s : Solution realAnalysis} (hs : IsWitness c s)
    (x : RSpace) (i : Fin 3) :
    timeJetField s 1 x i = heatStep (timeJetField s 0) x i -
      transport (timeJetField s 0) (timeJetField s 0) x i -
      spatialDerivative i (pressureJet s 0) x := by
  have h0 : timeJetField s 0 = fun y => s.velocity y 0 := by
    funext y j
    simp [timeJetField, rightJet]
  have hp : pressureJet s 0 = fun y => s.pressure y 0 := by
    funext y
    simp [pressureJet, rightJet]
  simpa [rightJet, rawRHS, h0, hp] using raw_time_jet hs 0 x i

/-- Only expansion of the explicit spatial expression is required for
positive orders. The right-time PDE and order zero are already proved. -/
def HigherRawExpansion (δ : ℝ) : Prop :=
  ∀ c ∈ Ioo 0 δ, ∀ s : Solution realAnalysis, IsWitness c s → ∀ (m : ℕ) (x : RSpace) (i : Fin 3),
    rightJet (rawRHS s x i) (m+1) = heatStep (timeJetField s (m+1)) x i -
      (∑ j ∈ Finset.range ((m+1)+1), ((m+1).choose j : ℝ) *
        transport (timeJetField s j) (timeJetField s ((m+1)-j)) x i) -
      spatialDerivative i (pressureJet s (m+1)) x

theorem differentiatedMomentum_of_higher_raw {δ : ℝ} (hexp : HigherRawExpansion δ) :
    DifferentiatedMomentum δ := by
  intro c hc s hs n x i
  cases n with
  | zero => simpa using raw_first_jet hs x i
  | succ m => exact (raw_time_jet hs (m+1) x i).trans (hexp c hc s hs m x i)

end
end CondFeffA

#print axioms CondFeffA.raw_time_jet
#print axioms CondFeffA.differentiatedMomentum_of_higher_raw
