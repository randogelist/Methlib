import CondMixed

namespace CondFeffA

open Fefferman Fefferman.ConcreteReal Set
open scoped BigOperators

noncomputable section

private abbrev STField := (RSpace × ℝ) → ℝ
private abbrev STSmooth (F : STField) := ContDiffOn ℝ ⊤ F {z | 0 ≤ z.2}
private def timeRead (F : STField) (n : ℕ) (x : RSpace) : ℝ :=
  rightJet (fun t => F (x,t)) n

private def coordPartial (j : Fin 3) (F : STField) : STField :=
  fun z => spatialDerivative j (fun y => F (y,z.2)) z.1

private lemma timeRead_partial {F : STField} (hF : STSmooth F) (j : Fin 3) (n : ℕ) :
    timeRead (coordPartial j F) n = spatialDerivative j (timeRead F n) :=
  funext (raw_space_time_commute hF j n)

private lemma slicedAt {F : STField} (hF : STSmooth F) (x : RSpace) (n : ℕ) :
    ContDiffWithinAt ℝ n (fun t => F (x,t)) (Ici 0) 0 :=
  ((slicing hF x) 0 (Set.self_mem_Ici : (0 : ℝ) ∈ Set.Ici 0)).of_le le_top

private lemma timeRead_add {F G : STField} (hF : STSmooth F) (hG : STSmooth G)
    (n : ℕ) (x : RSpace) :
    timeRead (F+G) n x = timeRead F n x + timeRead G n x :=
  iteratedDerivWithin_add (s := Ici (0 : ℝ)) (x := 0) (Set.self_mem_Ici : (0 : ℝ) ∈ Set.Ici 0) (uniqueDiffOn_Ici 0)
    (slicedAt hF x n) (slicedAt hG x n)

private lemma timeRead_sub {F G : STField} (hF : STSmooth F) (hG : STSmooth G)
    (n : ℕ) (x : RSpace) :
    timeRead (F-G) n x = timeRead F n x - timeRead G n x :=
  iteratedDerivWithin_sub (s := Ici (0 : ℝ)) (x := 0) (Set.self_mem_Ici : (0 : ℝ) ∈ Set.Ici 0) (uniqueDiffOn_Ici 0)
    (slicedAt hF x n) (slicedAt hG x n)

private lemma timeRead_mul {F G : STField} (hF : STSmooth F) (hG : STSmooth G)
    (n : ℕ) (x : RSpace) :
    timeRead (F*G) n x = ∑ a ∈ Finset.range (n+1),
      (n.choose a : ℝ) * timeRead F a x * timeRead G (n-a) x :=
  iteratedDerivWithin_mul (s := Ici (0 : ℝ)) (x := 0) (Set.self_mem_Ici : (0 : ℝ) ∈ Set.Ici 0) (uniqueDiffOn_Ici 0)
    (slicedAt hF x n) (slicedAt hG x n)

/-- Differentiate the three spatial diffusion terms, three transport products,
and pressure term of the literal momentum RHS. -/
theorem concrete_raw_expansion {c : ℝ} {s : Solution realAnalysis} (hs : IsWitness c s)
    (n : ℕ) (x : RSpace) (i : Fin 3) :
    rightJet (rawRHS s x i) n = heatStep (timeJetField s n) x i -
      (∑ a ∈ Finset.range (n+1), (n.choose a : ℝ) *
        transport (timeJetField s a) (timeJetField s (n-a)) x i) -
      spatialDerivative i (pressureJet s n) x := by
  let u (j : Fin 3) : STField := fun z => s.velocity z.1 z.2 j
  let p : STField := fun z => s.pressure z.1 z.2
  let H (j : Fin 3) := coordPartial j (coordPartial j (u i))
  let B (j : Fin 3) := u j * coordPartial j (u i)
  let P := coordPartial i p
  have h6 : clause06 realAnalysis s := hs.2.2.2.1
  have hu (j : Fin 3) : STSmooth (u j) := h6.1 j
  have hp : STSmooth p := h6.2
  have hP : STSmooth P := spatialSlice_smooth hp i
  have hX (j : Fin 3) : STSmooth (coordPartial j (u i)) := spatialSlice_smooth (hu i) j
  have hH (j : Fin 3) : STSmooth (H j) := spatialSlice_smooth (hX j) j
  have hB (j : Fin 3) : STSmooth (B j) := (hu j).mul (hX j)
  have hHeat (j : Fin 3) : timeRead (H j) n x =
      spatialDerivative j (spatialDerivative j (fun y => timeJetField s n y i)) x := by
    change timeRead (coordPartial j (coordPartial j (u i))) n x = _
    rw [timeRead_partial (hX j) j n, timeRead_partial (hu i) j n] <;> rfl
  have hTransport (j : Fin 3) : timeRead (B j) n x =
      ∑ a ∈ Finset.range (n+1), (n.choose a : ℝ) * timeJetField s a x j *
        spatialDerivative j (fun y => timeJetField s (n-a) y i) x := by
    change timeRead (u j * coordPartial j (u i)) n x = _
    rw [timeRead_mul (hu j) (hX j)]
    apply Finset.sum_congr rfl
    intro a ha
    rw [timeRead_partial (hu i) j (n-a)] <;> rfl
  have hPr : timeRead P n x = spatialDerivative i (pressureJet s n) x :=
    congrFun (timeRead_partial hp i n) x
  have conv : (timeRead (B 0) n x + timeRead (B 1) n x) + timeRead (B 2) n x =
      ∑ a ∈ Finset.range (n+1), (n.choose a : ℝ) *
        transport (timeJetField s a) (timeJetField s (n-a)) x i := by
    rw [hTransport 0, hTransport 1, hTransport 2]
    simp only [transport, sum3, mul_add, Finset.sum_add_distrib, mul_assoc]
  have HH : STSmooth (H 0 + H 1 + H 2) := ((hH 0).add (hH 1)).add (hH 2)
  have BB : STSmooth (B 0 + B 1 + B 2) := ((hB 0).add (hB 1)).add (hB 2)
  change timeRead ((H 0 + H 1 + H 2 - (B 0 + B 1 + B 2)) - P) n x = _
  rw [timeRead_sub (F := (H 0 + H 1 + H 2) - (B 0 + B 1 + B 2)) (G := P)
        (HH.sub BB) hP n x,
    timeRead_sub (F := H 0 + H 1 + H 2) (G := B 0 + B 1 + B 2) HH BB n x,
    timeRead_add (F := H 0 + H 1) (G := H 2) ((hH 0).add (hH 1)) (hH 2) n x,
    timeRead_add (F := H 0) (G := H 1) (hH 0) (hH 1) n x,
    timeRead_add (F := B 0 + B 1) (G := B 2) ((hB 0).add (hB 1)) (hB 2) n x,
    timeRead_add (F := B 0) (G := B 1) (hB 0) (hB 1) n x,
    conv, hHeat 0, hHeat 1, hHeat 2, hPr] <;> rfl

theorem concrete_higher_raw_expansion (δ : ℝ) : HigherRawExpansion δ :=
  fun _ _ _ hs m x i => concrete_raw_expansion hs (m+1) x i

end
end CondFeffA

#print axioms CondFeffA.concrete_raw_expansion
#print axioms CondFeffA.concrete_higher_raw_expansion
