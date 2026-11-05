import FEF_A_POSITIVE_TIME

set_option autoImplicit false

open scoped ContDiff

namespace Fefferman.ConcreteReal.AdjustedA
namespace ZeroSeed

noncomputable def zeroSolution : Solution realAnalysis where
  velocity := zeroRForce
  pressure := fun _ _ => 0

private theorem dx_const_zero (j : Fin 3) :
    spatialDerivative j (fun _ : RSpace => (0 : ℝ)) = fun _ => 0 := by
  funext x
  change (fderiv ℝ (fun _ : RSpace => (0 : ℝ)) x) (basisDirection j) = 0
  rw [fderiv_const_apply (𝕜 := ℝ) (x := x) (0 : ℝ)] <;> rfl

private theorem laplacian_const_zero (x : RSpace) :
    laplacian realAnalysis (fun _ : RSpace => (0 : ℝ)) x = 0 := by
  change sum3 realAnalysis
    (fun j => spatialDerivative j (spatialDerivative j (fun _ : RSpace => (0 : ℝ))) x) = 0
  simp [sum3, realAnalysis, dx_const_zero]

theorem admissible_zero :
    admissibleInitial realAnalysis .wholeSpace zeroRInitial := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    change ContDiff ℝ ⊤ (fun _ : RSpace => (0 : ℝ))
    exact contDiff_const
  · intro x
    change sum3 realAnalysis
      (fun i => spatialDerivative i (fun _ : RSpace => (0 : ℝ)) x) = 0
    simp [sum3, realAnalysis, dx_const_zero]
  · intro α k
    refine ⟨(1 : ℝ), ?_, ?_⟩
    · change (0 : ℝ) < 1
      norm_num
    intro x
    rw [spatialJet_zeroRInitial]
    simp [zeroRInitial, realAnalysis, euclideanNorm3, normSq3]

theorem zero_ambient_analytic (i : Fin 3) :
    ContDiff ℝ ⊤ (fun z : RSpace × ℝ => zeroSolution.velocity z.1 z.2 i) ∧
    ContDiff ℝ ⊤ (fun z : RSpace × ℝ => zeroSolution.pressure z.1 z.2) := by
  change ContDiff ℝ ⊤ (fun _ : RSpace × ℝ => (0 : ℝ)) ∧
    ContDiff ℝ ⊤ (fun _ : RSpace × ℝ => (0 : ℝ))
  exact ⟨contDiff_const, contDiff_const⟩

private theorem zero_momentum (ν : PositiveViscosity realAnalysis) :
    clause01 realAnalysis ν (zeroForce realAnalysis) zeroSolution := by
  intro x t _ i
  change timeDerivative (fun _ : ℝ => (0 : ℝ)) t +
    sum3 realAnalysis (fun j => (0 : ℝ) * spatialDerivative j (fun _ : RSpace => (0 : ℝ)) x) =
    ν.val * laplacian realAnalysis (fun _ : RSpace => (0 : ℝ)) x +
      -(spatialDerivative i (fun _ : RSpace => (0 : ℝ)) x) + 0
  rw [laplacian_const_zero x]
  simp [dx_const_zero, timeDerivative, sum3, realAnalysis]

theorem zero_global (ν : PositiveViscosity realAnalysis) :
    globalSolution realAnalysis .wholeSpace ν zeroRInitial (zeroForce realAnalysis)
      zeroSolution := by
  refine ⟨zero_momentum ν, ?_, ?_, ⟨zeroRForce_vectorSmooth, ?_⟩, ?_⟩
  · intro x t _
    change sum3 realAnalysis
      (fun i => spatialDerivative i (fun _ : RSpace => (0 : ℝ)) x) = 0
    simp [sum3, realAnalysis, dx_const_zero]
  · intro x
    rfl
  · exact ((zero_ambient_analytic 0).2).contDiffOn
  · refine ⟨(1 : ℝ), ?_, ?_⟩
    · change (0 : ℝ) < 1
      norm_num
    intro t _
    constructor
    · change MeasureTheory.Integrable (fun x : RSpace => normSq3 (zeroRForce x t))
      simp [zeroRForce, normSq3]
    · change (∫ x : RSpace, normSq3 (zeroRForce x t)) < (1 : ℝ)
      simp [zeroRForce, normSq3]

theorem zero_hasGlobalSolution (ν : PositiveViscosity realAnalysis) :
    hasGlobalSolution realAnalysis .wholeSpace ν zeroRInitial (zeroForce realAnalysis) :=
  ⟨zeroSolution, zero_global ν⟩

theorem zero_small (ε : ℝ) (hε : 0 < ε) (ν : PositiveViscosity realAnalysis) :
    SmallSchwartzSeed ε ν zeroRInitial := by
  refine {
    smooth := ?_
    solenoidal := admissible_zero.2.1
    decay := admissible_zero.2.2
    integrableCube := ?_
    smallCube := ?_ }
  · intro i
    change ContDiff ℝ ∞ (fun _ : RSpace => (0 : ℝ))
    exact contDiff_const
  · simp [zeroRInitial, euclideanNorm3, normSq3]
  · have hν : (0 : ℝ) < ν.val := ν.property
    simpa [zeroRInitial, euclideanNorm3, normSq3] using
      (pow_pos (mul_pos hε hν) 3)

theorem zero_positive_flow (ν : PositiveViscosity realAnalysis) :
    GlobalPositiveFlow ν zeroRInitial zeroSolution := by
  have h := zero_global ν
  refine {
    momentum := h.1
    solenoidal := h.2.1
    initial := h.2.2.1
    smoothVelocity := ?_
    analyticVelocity := ?_
    analyticPressure := ?_
    energy := h.2.2.2.2 }
  · intro i
    change ContDiffOn ℝ ∞ (fun _ : RSpace × ℝ => (0 : ℝ))
      {z : RSpace × ℝ | 0 ≤ z.2}
    exact contDiff_const.contDiffOn
  · intro i
    exact ((zero_ambient_analytic i).1).contDiffOn
  · exact ((zero_ambient_analytic 0).2).contDiffOn

end ZeroSeed

theorem zero_is_positive_time_state (ε : ℝ) (hε : 0 < ε)
    (ν : PositiveViscosity realAnalysis) : PositiveTimeState ε ν zeroRInitial := by
  refine ⟨zeroRInitial, (1 : ℝ), ZeroSeed.zeroSolution,
    ZeroSeed.zero_small ε hε ν, by norm_num, ZeroSeed.zero_positive_flow ν, ?_⟩
  rfl

end Fefferman.ConcreteReal.AdjustedA

#print axioms Fefferman.ConcreteReal.AdjustedA.ZeroSeed.admissible_zero
#print axioms Fefferman.ConcreteReal.AdjustedA.ZeroSeed.zero_ambient_analytic
#print axioms Fefferman.ConcreteReal.AdjustedA.ZeroSeed.zero_global
#print axioms Fefferman.ConcreteReal.AdjustedA.ZeroSeed.zero_hasGlobalSolution
#print axioms Fefferman.ConcreteReal.AdjustedA.ZeroSeed.zero_small
#print axioms Fefferman.ConcreteReal.AdjustedA.ZeroSeed.zero_positive_flow
#print axioms Fefferman.ConcreteReal.AdjustedA.zero_is_positive_time_state
