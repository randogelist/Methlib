import CondRawExpand

namespace CondFeffA

open Fefferman Fefferman.ConcreteReal Set
open scoped BigOperators
noncomputable section

private abbrev SpaceTime := RSpace × ℝ
private abbrev timeHalf : Set SpaceTime := {z | 0 ≤ z.2}
private abbrev STAnalytic (F : SpaceTime → ℝ) := ContDiffOn ℝ ⊤ F timeHalf
local notation "D" => spatialDerivative
local notation "L" => laplacian realAnalysis

/-- The positive-time derivative field admits this analytic representative
    on the entire closed half-space, including its initial trace. -/
theorem wji_spacetime_analytic_timeJet {F : RSpace × ℝ → ℝ}
    (hF : ContDiffOn ℝ ⊤ F {z | 0 ≤ z.2}) (n : ℕ) :
    ContDiffOn ℝ ⊤ (fun z : RSpace × ℝ =>
      iteratedDerivWithin n (fun t => F (z.1,t)) (Ici 0) z.2) {z | 0 ≤ z.2} := by
  let jet (j : ℕ) (z : SpaceTime) := iteratedDerivWithin j (fun t => F (z.1,t)) (Ici 0) z.2
  have hj (j : ℕ) : STAnalytic (jet j) := by
    induction j with
    | zero => simpa [jet] using hF
    | succ j ih =>
      let e : SpaceTime := (0,1)
      have hd : ContDiffOn ℝ ⊤ (fderivWithin ℝ (jet j) timeHalf) timeHalf :=
        ih.fderivWithin raw_uniqueDiffOn le_top
      apply (hd.clm_apply (g := fun _ => e) contDiffOn_const).congr
      intro z hz
      let line : ℝ → SpaceTime := fun t => (z.1,t)
      have hl : HasDerivWithinAt line e (Ici 0) z.2 :=
        ((hasDerivAt_const z.2 z.1).prodMk (hasDerivAt_id z.2)).hasDerivWithinAt
      have hdiff := (ih.differentiableOn (by simp) z hz).hasFDerivWithinAt
      have hcomp := hdiff.comp_hasDerivWithinAt (f := line) z.2 hl (fun _ ht => ht)
      change iteratedDerivWithin (j+1) (fun t => F (z.1,t)) (Ici 0) z.2 = _
      rw [iteratedDerivWithin_succ]
      exact hcomp.derivWithin (uniqueDiffOn_Ici 0 z.2 hz)
  exact hj n

/-- Every right derivative of an analytic spacetime field has analytic spatial
    dependence on the initial face. -/
theorem wji_spatial_analytic_rightJet {F : RSpace × ℝ → ℝ}
    (hF : ContDiffOn ℝ ⊤ F {z | 0 ≤ z.2}) (n : ℕ) :
    ContDiff ℝ ⊤ (fun x : RSpace => rightJet (fun t => F (x,t)) n) := by
  exact (wji_spacetime_analytic_timeJet hF n).comp_contDiff
    (f := fun x : RSpace => (x, (0 : ℝ))) (contDiff_id.prodMk contDiff_const)
    (fun _ => (show (0 : ℝ) ≤ 0 from le_rfl))

theorem wji_velocityJet_analytic {c : ℝ} {s : Solution realAnalysis} (hs : IsWitness c s)
    (n : ℕ) (i : Fin 3) : ContDiff ℝ ⊤ (fun x => timeJetField s n x i) :=
  wji_spatial_analytic_rightJet (F := fun z => s.velocity z.1 z.2 i) (hs.2.2.2.1.1 i) n

theorem wji_pressureJet_analytic {c : ℝ} {s : Solution realAnalysis} (hs : IsWitness c s)
    (n : ℕ) : ContDiff ℝ ⊤ (pressureJet s n) :=
  wji_spatial_analytic_rightJet (F := fun z => s.pressure z.1 z.2) hs.2.2.2.1.2 n

private lemma rightJet_add_at_face {f g : ℝ → ℝ} (n : ℕ)
    (hf : ContDiffOn ℝ ⊤ f (Ici 0)) (hg : ContDiffOn ℝ ⊤ g (Ici 0)) :
    rightJet (f+g) n = rightJet f n + rightJet g n :=
  iteratedDerivWithin_add (s := Ici (0:ℝ)) (x := 0) (self_mem_Ici : (0:ℝ) ∈ Ici 0)
    (uniqueDiffOn_Ici 0) ((hf 0 self_mem_Ici).of_le le_top) ((hg 0 self_mem_Ici).of_le le_top)

/-- Clause 02 and commuting one spatial derivative with the right jet give
    solenoidality at every order without a pressure or Sobolev premise. -/
theorem wji_timeJet_div_zero {c : ℝ} {s : Solution realAnalysis} (hs : IsWitness c s)
    (n : ℕ) : fieldDiv (timeJetField s n) = 0 := by
  funext x
  let f (j : Fin 3) (t : ℝ) := D j (fun y => s.velocity y t j) x
  have hf (j : Fin 3) : ContDiffOn ℝ ⊤ (f j) (Ici 0) :=
    slicing (spatialSlice_smooth (F := fun z => s.velocity z.1 z.2 j)
      (hs.2.2.2.1.1 j) j) x
  have hj (j : Fin 3) : rightJet (f j) n = D j (fun y => timeJetField s n y j) x :=
    raw_space_time_commute (F := fun z => s.velocity z.1 z.2 j) (hs.2.2.2.1.1 j) j n x
  have heq : EqOn (f 0 + f 1 + f 2) (0 : ℝ → ℝ) (Ici 0) := by
    intro t ht
    exact hs.2.1 x t ht
  have hz : rightJet (f 0 + f 1 + f 2) n = 0 := by
    calc
      _ = rightJet (0 : ℝ → ℝ) n :=
        iteratedDerivWithin_congr (n := n) heq (self_mem_Ici : (0:ℝ) ∈ Ici 0)
      _ = 0 := by simp [rightJet]
  rw [rightJet_add_at_face (f := f 0 + f 1) (g := f 2) n ((hf 0).add (hf 1)) (hf 2),
    rightJet_add_at_face (f := f 0) (g := f 1) n (hf 0) (hf 1), hj 0, hj 1, hj 2] at hz
  exact hz

def wjiJetPressureGradient (s : Solution realAnalysis) (n : ℕ) : RInitial :=
  fun x i => D i (pressureJet s n) x

theorem wji_raw_field_balance {c : ℝ} {s : Solution realAnalysis} (hs : IsWitness c s) (n : ℕ) :
    timeJetField s (n+1) = heatStep (timeJetField s n) -
      (∑ j ∈ Finset.range (n+1), (n.choose j : ℝ) •
        transport (timeJetField s j) (timeJetField s (n-j))) - wjiJetPressureGradient s n := by
  funext x i
  simpa only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, wjiJetPressureGradient]
    using (raw_time_jet hs n x i).trans (concrete_raw_expansion hs n x i)

private theorem jetLapAnalytic {f : RSpace → ℝ} (hf : ContDiff ℝ ⊤ f) :
    ContDiff ℝ ⊤ (L f) := by
  exact ((partial_analytic (partial_analytic hf 0) 0).add
    (partial_analytic (partial_analytic hf 1) 1)).add
    (partial_analytic (partial_analytic hf 2) 2)

private theorem jetLapAdd {f g : RSpace → ℝ}
    (hf : ContDiff ℝ ⊤ f) (hg : ContDiff ℝ ⊤ g) :
    L (fun x => f x + g x) = fun x => L f x + L g x := by
  have move (i : Fin 3) (x : RSpace) :
      D i (D i (fun y => f y + g y)) x = D i (D i f) x + D i (D i g) x := by
    have he : D i (fun y => f y + g y) = fun y => D i f y + D i g y :=
      funext (partial_add hf hg i)
    rw [he]
    exact partial_add (partial_analytic hf i) (partial_analytic hg i) i x
  funext x
  change D 0 (D 0 _) x + D 1 (D 1 _) x + D 2 (D 2 _) x =
    (D 0 (D 0 f) x + D 1 (D 1 f) x + D 2 (D 2 f) x) +
    (D 0 (D 0 g) x + D 1 (D 1 g) x + D 2 (D 2 g) x)
  rw [move 0 x, move 1 x, move 2 x]
  ring

private theorem jetLapPartial {f : RSpace → ℝ} (hf : ContDiff ℝ ⊤ f) (i : Fin 3) :
    L (D i f) = D i (L f) := by
  let hdiag (j : Fin 3) := partial_analytic (partial_analytic hf j) j
  have move (j : Fin 3) (x : RSpace) :
      D j (D j (D i f)) x = D i (D j (D j f)) x := by
    have he : D j (D i f) = D i (D j f) := funext (partial_comm hf j i)
    rw [he]
    exact partial_comm (partial_analytic hf j) j i x
  funext x
  change D 0 (D 0 (D i f)) x + D 1 (D 1 (D i f)) x + D 2 (D 2 (D i f)) x =
    D i (fun y => D 0 (D 0 f) y + D 1 (D 1 f) y + D 2 (D 2 f) y) x
  rw [partial_add ((hdiag 0).add (hdiag 1)) (hdiag 2),
    partial_add (hdiag 0) (hdiag 1), move 0 x, move 1 x, move 2 x]

/-- Taking the divergence and the componentwise heat operator commute on
    spatially analytic fields. -/
theorem wji_fieldDiv_heat {v : RInitial}
    (hv : ∀ i, ContDiff ℝ ⊤ (fun x => v x i)) :
    fieldDiv (heatStep v) = L (fieldDiv v) := by
  let f (i : Fin 3) := fun x : RSpace => v x i
  have hd (i : Fin 3) : ContDiff ℝ ⊤ (D i (f i)) := partial_analytic (hv i) i
  change (fun x => D 0 (L (f 0)) x + D 1 (L (f 1)) x + D 2 (L (f 2)) x) =
    L (fun x => D 0 (f 0) x + D 1 (f 1) x + D 2 (f 2) x)
  rw [jetLapAdd (f := fun x => D 0 (f 0) x + D 1 (f 1) x) (g := D 2 (f 2))
        ((hd 0).add (hd 1)) (hd 2),
    jetLapAdd (f := D 0 (f 0)) (g := D 1 (f 1)) (hd 0) (hd 1),
    jetLapPartial (f := f 0) (hv 0) 0, jetLapPartial (f := f 1) (hv 1) 1,
    jetLapPartial (f := f 2) (hv 2) 2]

theorem wji_heat_timeJet_div_zero {c : ℝ} {s : Solution realAnalysis} (hs : IsWitness c s)
    (n : ℕ) : fieldDiv (heatStep (timeJetField s n)) = 0 := by
  rw [wji_fieldDiv_heat (v := timeJetField s n) (wji_velocityJet_analytic hs n), wji_timeJet_div_zero hs n]
  have d0 (j : Fin 3) : D j (0 : RSpace → ℝ) = 0 := by
    funext x
    change (fderiv ℝ (fun _ : RSpace => (0 : ℝ)) x) (basisDirection j) = 0
    rw [fderiv_const_apply] <;> rfl
  funext x
  change D 0 (D 0 (0 : RSpace → ℝ)) x + D 1 (D 1 (0 : RSpace → ℝ)) x +
    D 2 (D 2 (0 : RSpace → ℝ)) x = 0
  simp only [d0, Pi.zero_apply, add_zero]

private lemma jetDivAdd {u v : RInitial}
    (hu : ∀ i, ContDiff ℝ ⊤ (fun x => u x i))
    (hv : ∀ i, ContDiff ℝ ⊤ (fun x => v x i)) :
    fieldDiv (u+v) = fieldDiv u + fieldDiv v := by
  funext x
  have h (i : Fin 3) :
      D i (fun y => (u+v) y i) x = D i (fun y => u y i) x + D i (fun y => v y i) x :=
    partial_add (hu i) (hv i) i x
  change D 0 (fun y => (u+v) y 0) x + D 1 (fun y => (u+v) y 1) x +
      D 2 (fun y => (u+v) y 2) x =
    (D 0 (fun y => u y 0) x + D 1 (fun y => u y 1) x + D 2 (fun y => u y 2) x) +
    (D 0 (fun y => v y 0) x + D 1 (fun y => v y 1) x + D 2 (fun y => v y 2) x)
  rw [h 0, h 1, h 2]
  ring

/-- The pressure jet solves the physical Poisson equation, directly from
    clauses 01, 02 and closed-half-space analyticity. A harmonic pressure
    ambiguity still has to be removed to identify the Newton potential. -/
theorem wji_pressureJet_poisson {c : ℝ} {s : Solution realAnalysis} (hs : IsWitness c s) (n : ℕ) :
    L (pressureJet s n) =
      -fieldDiv (∑ j ∈ Finset.range (n+1), (n.choose j : ℝ) •
        transport (timeJetField s j) (timeJetField s (n-j))) := by
  let U := timeJetField s
  let B : RInitial := ∑ j ∈ Finset.range (n+1), (n.choose j : ℝ) • transport (U j) (U (n-j))
  let P := wjiJetPressureGradient s n
  have raw : U (n+1) = heatStep (U n) - B - P := wji_raw_field_balance hs n
  have heB : B = heatStep (U n) - P - U (n+1) := by rw [raw]; abel
  have heH : heatStep (U n) = (U (n+1) + B) + P := by rw [raw]; abel
  have hP (i : Fin 3) : ContDiff ℝ ⊤ (fun x => P x i) :=
    partial_analytic (wji_pressureJet_analytic hs n) i
  have hB (i : Fin 3) : ContDiff ℝ ⊤ (fun x => B x i) := by
    rw [heB]
    exact ((jetLapAnalytic (wji_velocityJet_analytic hs n i)).sub (hP i)).sub
      (wji_velocityJet_analytic hs (n+1) i)
  have hplus (i : Fin 3) : ContDiff ℝ ⊤ (fun x => (U (n+1) + B) x i) :=
    (wji_velocityJet_analytic hs (n+1) i).add (hB i)
  have hz : (0 : RSpace → ℝ) = (fieldDiv (U (n+1)) + fieldDiv B) + fieldDiv P := by
    calc
      _ = fieldDiv (heatStep (U n)) := (wji_heat_timeJet_div_zero hs n).symm
      _ = fieldDiv ((U (n+1) + B) + P) := congrArg fieldDiv heH
      _ = _ := by
        rw [jetDivAdd (u := U (n+1) + B) (v := P) hplus hP,
          jetDivAdd (u := U (n+1)) (v := B) (wji_velocityJet_analytic hs (n+1)) hB]
  have hu0 : fieldDiv (U (n+1)) = 0 := wji_timeJet_div_zero hs (n+1)
  rw [hu0, zero_add] at hz
  funext x
  have hx := congrFun hz x
  change (0 : ℝ) = fieldDiv B x + fieldDiv P x at hx
  change fieldDiv P x = -(fieldDiv B x)
  linarith only [hx]


open MeasureTheory

/-- No global bound on the pressure jet is needed for its compactly
    supported solenoidal test pairing to vanish. -/
theorem wji_pressureJet_annihilates_tests {c : ℝ} {s : Solution realAnalysis}
    (hs : IsWitness c s) (n : ℕ) (φ : RInitial)
    (hφ : ∀ i, ContDiff ℝ 1 (fun x => φ x i))
    (hk : ∀ i, HasCompactSupport (fun x => φ x i)) (hdiv : fieldDiv φ = 0) :
    (∫ x, ∑ i : Fin 3, φ x i * wjiJetPressureGradient s n x i) = 0 := by
  let p := pressureJet s n
  let f (i : Fin 3) := fun x : RSpace => φ x i
  let A (i : Fin 3) := fun x => f i x * D i p x
  let B (i : Fin 3) := fun x => D i (f i) x * p x
  have hp : ContDiff ℝ ⊤ p := wji_pressureJet_analytic hs n
  have hD (i : Fin 3) : Continuous (D i (f i)) :=
    ((hφ i).continuous_fderiv_apply (by simp)).comp (continuous_id.prodMk continuous_const)
  have hDK (i : Fin 3) : HasCompactSupport (D i (f i)) :=
    (hk i).fderiv_apply ℝ (basisDirection i)
  have hA (i : Fin 3) : Integrable (A i) :=
    ((hφ i).continuous.mul (partial_analytic hp i).continuous).integrable_of_hasCompactSupport
      (hk i).mul_right
  have hB (i : Fin 3) : Integrable (B i) :=
    ((hD i).mul hp.continuous).integrable_of_hasCompactSupport (hDK i).mul_right
  have hprod (i : Fin 3) : Integrable (fun x => f i x * p x) :=
    ((hφ i).continuous.mul hp.continuous).integrable_of_hasCompactSupport (hk i).mul_right
  have hibp (i : Fin 3) : (∫ x, A i x) = -(∫ x, B i x) :=
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      (f := f i) (g := p) (μ := volume) (v := basisDirection i)
      (hB i) (hA i) (hprod i) (fun x _ => (hφ i).differentiable (by simp) x)
      (fun x _ => hp.differentiable (by simp) x)
  have hzero (x : RSpace) : (∑ i : Fin 3, B i x) = 0 := by
    have hz := congrFun hdiv x
    change D 0 (f 0) x + D 1 (f 1) x + D 2 (f 2) x = 0 at hz
    change (∑ i : Fin 3, D i (f i) x * p x) = 0
    rw [← Finset.sum_mul, Fin.sum_univ_three, hz, zero_mul]
  change (∫ x, ∑ i : Fin 3, A i x) = 0
  calc
    _ = ∑ i : Fin 3, ∫ x, A i x :=
      integral_finsetSum Finset.univ (f := A) (fun i _ => hA i)
    _ = ∑ i : Fin 3, -(∫ x, B i x) :=
      Finset.sum_congr rfl (fun i _ => hibp i)
    _ = -(∑ i : Fin 3, ∫ x, B i x) := by rw [Finset.sum_neg_distrib]
    _ = -(∫ x, ∑ i : Fin 3, B i x) :=
      congrArg (fun a : ℝ => -a) (integral_finsetSum Finset.univ (f := B) (fun i _ => hB i)).symm
    _ = 0 := by simp only [hzero, integral_zero, neg_zero]


/-- The pressure-free differentiated momentum equation holds in all compact
    solenoidal test directions, for the actual jets of the literal witness. -/
theorem wji_raw_solenoidal_test_balance {c : ℝ} {s : Solution realAnalysis}
    (hs : IsWitness c s) (n : ℕ) (φ : RInitial)
    (hφ : ∀ i, ContDiff ℝ 1 (fun x => φ x i))
    (hk : ∀ i, HasCompactSupport (fun x => φ x i)) (hdiv : fieldDiv φ = 0) :
    (∫ x, ∑ i : Fin 3, φ x i * (timeJetField s (n+1) - heatStep (timeJetField s n) +
      (∑ j ∈ Finset.range (n+1), (n.choose j : ℝ) •
        transport (timeJetField s j) (timeJetField s (n-j)))) x i) = 0 := by
  let B : RInitial := ∑ j ∈ Finset.range (n+1), (n.choose j : ℝ) •
    transport (timeJetField s j) (timeJetField s (n-j))
  have hm : timeJetField s (n+1) = heatStep (timeJetField s n) - B -
      wjiJetPressureGradient s n := wji_raw_field_balance hs n
  have he : timeJetField s (n+1) - heatStep (timeJetField s n) + B =
      -wjiJetPressureGradient s n := by rw [hm]; abel
  change (∫ x, ∑ i : Fin 3, φ x i *
    (timeJetField s (n+1) - heatStep (timeJetField s n) + B) x i) = 0
  rw [he]
  simp only [Pi.neg_apply, mul_neg, Finset.sum_neg_distrib, integral_neg,
    wji_pressureJet_annihilates_tests hs n φ hφ hk hdiv, neg_zero]

end
end CondFeffA

#print axioms CondFeffA.wji_spacetime_analytic_timeJet
#print axioms CondFeffA.wji_spatial_analytic_rightJet
#print axioms CondFeffA.wji_velocityJet_analytic
#print axioms CondFeffA.wji_pressureJet_analytic
#print axioms CondFeffA.wji_timeJet_div_zero
#print axioms CondFeffA.wji_raw_field_balance
#print axioms CondFeffA.wji_fieldDiv_heat
#print axioms CondFeffA.wji_heat_timeJet_div_zero
#print axioms CondFeffA.wji_pressureJet_poisson

#print axioms CondFeffA.wji_pressureJet_annihilates_tests
#print axioms CondFeffA.wji_raw_solenoidal_test_balance
