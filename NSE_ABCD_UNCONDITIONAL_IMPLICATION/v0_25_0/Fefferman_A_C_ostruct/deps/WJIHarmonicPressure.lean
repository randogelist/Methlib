import WJIPhysicalProjection
import WJIGradientLiouville

namespace CondFeffA

open Fefferman Fefferman.ConcreteReal WJISmooth
open scoped ContDiff BigOperators
noncomputable section

def WJIJetsInSobolevSpace (δ : ℝ) : Prop :=
  ∀ c ∈ Set.Ioo 0 δ, ∀ s : Solution realAnalysis, IsWitness c s →
    ∀ n : ℕ, timeJetField s n ∈ WJISobolev.space

/-- The original pressure gauge does not enter. Solving the raw momentum
    identity for its gradient bounds it in the same space as the jets. -/
theorem wji_witness_pressureGradient_mem {c : ℝ} {s : Solution realAnalysis}
    (hs : IsWitness c s) (hjet : ∀ n : ℕ, timeJetField s n ∈ WJISobolev.space)
    (n : ℕ) : wjiJetPressureGradient s n ∈ WJISobolev.space := by
  let U (j : ℕ) : WJISobolev.space := ⟨timeJetField s j, hjet j⟩
  let B : RInitial := ∑ j ∈ Finset.range (n+1), (n.choose j : ℝ) •
    transport (timeJetField s j) (timeJetField s (n-j))
  have hB : B ∈ WJISobolev.space :=
    WJISobolev.space.sum_mem (fun j _ =>
      WJISobolev.space.smul_mem _ (WJISobolev.transport_mem (U j) (U (n-j))))
  have raw : timeJetField s (n+1) = heatStep (timeJetField s n) - B -
      wjiJetPressureGradient s n := wji_raw_field_balance hs n
  have eq : wjiJetPressureGradient s n = heatStep (timeJetField s n) - B -
      timeJetField s (n+1) := by rw [raw]; abel
  rw [eq]
  exact WJISobolev.space.sub_mem
    (WJISobolev.space.sub_mem (WJISobolev.heat_mem (U n)) hB) (hjet (n+1))

private def gradientMap : scalarSpace →ₗ[ℝ] RInitial where
  toFun q := wjiScalarGradient q.val
  map_add' q r := by
    funext x i
    exact congrArg (fun f : scalarSpace => f.val x) ((partialMap i).map_add q r)
  map_smul' a q := by
    funext x i
    exact congrArg (fun f : scalarSpace => f.val x) ((partialMap i).map_smul a q)

private def laplaceMap : scalarSpace →ₗ[ℝ] (RSpace → ℝ) :=
  scalarSpace.subtype.comp ((partialMap 0).comp (partialMap 0) +
    (partialMap 1).comp (partialMap 1) + (partialMap 2).comp (partialMap 2))

private def coordMap (i : Fin 3) : WJISobolev.space →ₗ[ℝ] scalarSpace where
  toFun F := ⟨fun x => F.val x i, WJISobolev.scalar_smooth (F.property i)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def divergenceMap : WJISobolev.space →ₗ[ℝ] (RSpace → ℝ) :=
  scalarSpace.subtype.comp ((partialMap 0).comp (coordMap 0) +
    (partialMap 1).comp (coordMap 1) + (partialMap 2).comp (coordMap 2))

private theorem gradientMap_val (q : scalarSpace) :
    gradientMap q = wjiScalarGradient q.val := rfl

/-- Summing the uniquely normalized Newton gradients at the differentiated
    transport sources determines the actual pressure gradient at the initial
    face. The harmonic difference is removed by square integrability. -/
theorem wji_pressure_identification_of_poisson {δ : ℝ}
    (hjet : WJIJetsInSobolevSpace δ) (hN : NewtonPoissonOn)
    (hSmooth : ∀ v w : WJISobolev.space, ContDiff ℝ ∞ (wjiNewtonScalar v.val w.val)) :
    PressureGradientIdentification δ := by
  intro c hc s hs n x i
  let U (j : ℕ) : WJISobolev.space := ⟨timeJetField s j, hjet c hc s hs j⟩
  let A (j : ℕ) : WJISobolev.space :=
    ⟨transport (U j).val (U (n-j)).val, WJISobolev.transport_mem (U j) (U (n-j))⟩
  let N (j : ℕ) : scalarSpace :=
    ⟨wjiNewtonScalar (U j).val (U (n-j)).val, hSmooth (U j) (U (n-j))⟩
  let Q : scalarSpace := ∑ j ∈ Finset.range (n+1), (n.choose j : ℝ) • N j
  let B : WJISobolev.space := ∑ j ∈ Finset.range (n+1), (n.choose j : ℝ) • A j
  have hB : B.val = ∑ j ∈ Finset.range (n+1), (n.choose j : ℝ) •
      transport (timeJetField s j) (timeJetField s (n-j)) := by
    change WJISobolev.space.subtype (∑ j ∈ Finset.range (n+1), (n.choose j : ℝ) • A j) = _
    simp only [map_sum, map_smul] <;> rfl
  have hgradient : wjiScalarGradient Q.val =
      ∑ j ∈ Finset.range (n+1), (n.choose j : ℝ) • wjiScalarGradient (N j).val := by
    calc
      _ = gradientMap (∑ j ∈ Finset.range (n+1), (n.choose j : ℝ) • N j) := rfl
      _ = ∑ j ∈ Finset.range (n+1), (n.choose j : ℝ) • gradientMap (N j) := by
        simp only [map_sum, map_smul]
      _ = _ := by simp only [gradientMap_val]
  have hgradQ : wjiScalarGradient Q.val ∈ WJISobolev.space := by
    rw [hgradient]
    exact WJISobolev.space.sum_mem (fun j _ =>
      WJISobolev.space.smul_mem _ (hN (U j) (U (n-j))).1)
  have hgradP : wjiScalarGradient (pressureJet s n) ∈ WJISobolev.space :=
    wji_witness_pressureGradient_mem hs (hjet c hc s hs) n
  have hlap (j : ℕ) : laplaceMap (N j) = -(divergenceMap (A j)) :=
    (hN (U j) (U (n-j))).2
  have hQlap : laplacian realAnalysis Q.val = -fieldDiv B.val := by
    change laplaceMap (∑ j ∈ Finset.range (n+1), (n.choose j : ℝ) • N j) =
      -divergenceMap (∑ j ∈ Finset.range (n+1), (n.choose j : ℝ) • A j)
    simp only [map_sum, map_smul, hlap, smul_neg, Finset.sum_neg_distrib]
  have hlaps : laplacian realAnalysis (pressureJet s n) = laplacian realAnalysis Q.val := by
    rw [hQlap, hB]
    exact wji_pressureJet_poisson hs n
  have h := wji_equal_gradients_of_laplacian (pressureJet s n) Q.val
    ((wji_pressureJet_analytic hs n).of_le le_top) Q.property
    (WJISobolev.space.sub_mem hgradP hgradQ) hlaps
  have result := congrFun (congrFun (h.trans hgradient) x) i
  calc
    spatialDerivative i (pressureJet s n) x =
        wjiScalarGradient (pressureJet s n) x i := rfl
    _ = ∑ j ∈ Finset.range (n+1), (n.choose j : ℝ) *
        wjiScalarGradient (N j).val x i := by
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using result
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      rfl

end
end CondFeffA

#print axioms CondFeffA.wji_witness_pressureGradient_mem
#print axioms CondFeffA.wji_pressure_identification_of_poisson
