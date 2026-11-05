import ShiftAnalytic
import ShiftCore

set_option autoImplicit false

open MeasureTheory
open scoped ContDiff

namespace Fefferman.ConcreteReal.AdjustedB

noncomputable section

/-- A unit cell for the coordinate periods of the concrete torus model. -/
def periodCell : Set RSpace := Set.Icc (0 : RSpace) (fun _ => (1 : ℝ))

/-- Smooth solenoidal periodic seed, small in the Euclidean L³ norm on one cell. -/
structure SmallPeriodicSeed (ε : ℝ) (ν : PositiveViscosity realAnalysis)
    (b : RInitial) : Prop where
  smooth : ∀ i : Fin 3, ContDiff ℝ ∞ (fun x => b x i)
  solenoidal : initialDivergenceFree realAnalysis b
  periodic : initialPeriodic realAnalysis b
  integrableCube : IntegrableOn (fun x => (euclideanNorm3 (b x)) ^ (3 : ℕ)) periodCell
  smallCube : (∫ x in periodCell, (euclideanNorm3 (b x)) ^ (3 : ℕ)) < (ε * ν.val) ^ (3 : ℕ)

/-- An exhibited unforced periodic ancestor. The velocity is smooth up to seed
time. The velocity and pressure are analytic jointly at positive elapsed times. -/
structure GlobalPositiveFlow (ν : PositiveViscosity realAnalysis) (b : RInitial)
    (s : Solution realAnalysis) : Prop where
  momentum : clause01 realAnalysis ν (zeroForce realAnalysis) s
  solenoidal : clause02 realAnalysis s
  initial : clause03 realAnalysis b s
  smoothVelocity : ∀ i : Fin 3,
    ContDiffOn ℝ ∞ (fun z : RSpace × ℝ => s.velocity z.1 z.2 i)
      {z : RSpace × ℝ | 0 ≤ z.2}
  analyticVelocity : ∀ i : Fin 3,
    ContDiffOn ℝ ⊤ (fun z : RSpace × ℝ => s.velocity z.1 z.2 i)
      {z : RSpace × ℝ | 0 < z.2}
  analyticPressure : ContDiffOn ℝ ⊤ (fun z : RSpace × ℝ => s.pressure z.1 z.2)
      {z : RSpace × ℝ | 0 < z.2}
  velocityPeriodic : clause10 realAnalysis s
  pressurePeriodic : periodicPressureErratum realAnalysis s

def PositiveTimeState (ε : ℝ) (ν : PositiveViscosity realAnalysis) (u₀ : RInitial) : Prop :=
  ∃ (b : RInitial) (τ : ℝ) (s : Solution realAnalysis),
    SmallPeriodicSeed ε ν b ∧ 0 < τ ∧ GlobalPositiveFlow ν b s ∧ shiftInitial s τ = u₀

theorem shift_clause10 (s : Solution realAnalysis) (τ : ℝ) (hτ : 0 ≤ τ)
    (h : clause10 realAnalysis s) : clause10 realAnalysis (shiftSolution s τ) := by
  intro x t ht j
  exact h x (t + τ) (add_nonneg ht hτ) j

theorem shift_periodic_pressure (s : Solution realAnalysis) (τ : ℝ) (hτ : 0 ≤ τ)
    (h : periodicPressureErratum realAnalysis s) :
    periodicPressureErratum realAnalysis (shiftSolution s τ) := by
  intro x t ht j
  exact h x (t + τ) (add_nonneg ht hτ) j

/-- Restart inside the analytic region and retain the period of both fields. -/
theorem shifted_global_solution (ν : PositiveViscosity realAnalysis)
    (b : RInitial) (s : Solution realAnalysis) (τ : ℝ) (hτ : 0 < τ)
    (hs : GlobalPositiveFlow ν b s) :
    globalSolution realAnalysis .periodic ν (shiftInitial s τ)
      (zeroForce realAnalysis) (shiftSolution s τ) := by
  refine ⟨shift_clause01 ν s τ hτ.le hs.momentum,
    shift_clause02 s τ hτ.le hs.solenoidal, shift_clause03 s τ,
    shift_clause10 s τ hτ.le hs.velocityPeriodic, ?_,
    shift_periodic_pressure s τ hτ.le hs.pressurePeriodic⟩
  constructor
  · intro i
    exact AdjustedA.smoothClosedHalfSpaceReal_shift (fun x t => s.velocity x t i)
      τ hτ (hs.analyticVelocity i)
  · exact AdjustedA.smoothClosedHalfSpaceReal_shift (fun x t => s.pressure x t)
      τ hτ hs.analyticPressure

/-- Restriction of the literal v0.25.0 B endpoint to admissible,
witnessed positive-time states of small unforced periodic flows. -/
def Fefferman_adjusted_B (ε : ℝ) : Prop :=
  ∀ (ν : PositiveViscosity realAnalysis) (u₀ : RInitial),
    admissibleInitial realAnalysis .periodic u₀ →
    PositiveTimeState ε ν u₀ →
    hasGlobalSolution realAnalysis .periodic ν u₀ (zeroForce realAnalysis)

theorem FEF_B_POSITIVE_TIME (ε : ℝ) : Fefferman_adjusted_B ε := by
  intro ν u₀ _hadm hu₀
  rcases hu₀ with ⟨b, τ, s, _, hτ, hs, htrace⟩
  subst u₀
  exact ⟨shiftSolution s τ, shifted_global_solution ν b s τ hτ hs⟩

def smoothOnSlab (τ : ℝ) (f : RSpace → ℝ → ℝ) : Prop :=
  ContDiffOn ℝ ∞ (fun z : RSpace × ℝ => f z.1 z.2)
    {z : RSpace × ℝ | 0 ≤ z.2 ∧ z.2 ≤ τ}

/-- Actual PDE history on the bounded slab, with periods for velocity and pressure. -/
structure FiniteHistory (ν : PositiveViscosity realAnalysis) (b : RInitial)
    (τ : ℝ) (s : Solution realAnalysis) : Prop where
  initial : clause03 realAnalysis b s
  velocitySmooth : ∀ i : Fin 3, smoothOnSlab τ (fun x t => s.velocity x t i)
  pressureSmooth : smoothOnSlab τ (fun x t => s.pressure x t)
  momentum : ∀ (x : RSpace) (t : ℝ), 0 < t → t < τ → ∀ i : Fin 3,
    timeDerivative (fun r => s.velocity x r i) t +
      sum3 realAnalysis (fun j => s.velocity x t j *
        spatialDerivative j (fun y => s.velocity y t i) x) =
        ν.val * laplacian realAnalysis (fun y => s.velocity y t i) x -
          spatialDerivative i (fun y => s.pressure y t) x
  solenoidal : ∀ (x : RSpace) (t : ℝ), 0 < t → t < τ →
    sum3 realAnalysis (fun i => spatialDerivative i (fun y => s.velocity y t i) x) = 0
  velocityPeriodic : ∀ (x : RSpace) (t : ℝ), 0 ≤ t → t ≤ τ → ∀ j : Fin 3,
    s.velocity (unitShift realAnalysis x j) t = s.velocity x t
  pressurePeriodic : ∀ (x : RSpace) (t : ℝ), 0 ≤ t → t ≤ τ → ∀ j : Fin 3,
    s.pressure (unitShift realAnalysis x j) t = s.pressure x t

def FinitePositiveTimeState (ε : ℝ) (ν : PositiveViscosity realAnalysis) (u₀ : RInitial) : Prop :=
  ∃ (b : RInitial) (τ : ℝ) (s : Solution realAnalysis),
    SmallPeriodicSeed ε ν b ∧ 0 < τ ∧ FiniteHistory ν b τ s ∧ shiftInitial s τ = u₀

/-- Independent premise: a global periodic flow exists from the seed and
agrees at the endpoint of each smooth periodic finite history from that seed. -/
def SeedExtension (ε : ℝ) : Prop :=
  ∀ (ν : PositiveViscosity realAnalysis) (b : RInitial), SmallPeriodicSeed ε ν b →
    ∃ s : Solution realAnalysis, GlobalPositiveFlow ν b s ∧
      ∀ (τ : ℝ) (h : Solution realAnalysis), 0 < τ → FiniteHistory ν b τ h →
        shiftInitial s τ = shiftInitial h τ

theorem regularity_of_seed_extension (ε : ℝ) (ext : SeedExtension ε)
    (ν : PositiveViscosity realAnalysis) (u₀ : RInitial)
    (hadm : admissibleInitial realAnalysis .periodic u₀)
    (hu₀ : FinitePositiveTimeState ε ν u₀) :
    hasGlobalSolution realAnalysis .periodic ν u₀ (zeroForce realAnalysis) := by
  rcases hu₀ with ⟨b, τ, h, hb, hτ, hh, htrace⟩
  rcases ext ν b hb with ⟨s, hs, hmatch⟩
  apply FEF_B_POSITIVE_TIME ε ν u₀ hadm
  exact ⟨b, τ, s, hb, hτ, hs, (hmatch τ h hτ hh).trans htrace⟩

end
end Fefferman.ConcreteReal.AdjustedB

set_option autoImplicit false

open scoped ContDiff

namespace Fefferman.ConcreteReal.AdjustedB
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
    admissibleInitial realAnalysis .periodic zeroRInitial := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    change ContDiff ℝ ⊤ (fun _ : RSpace => (0 : ℝ))
    exact contDiff_const
  · intro x
    change sum3 realAnalysis
      (fun i => spatialDerivative i (fun _ : RSpace => (0 : ℝ)) x) = 0
    simp [sum3, realAnalysis, dx_const_zero]
  · intro x j
    rfl

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
    globalSolution realAnalysis .periodic ν zeroRInitial (zeroForce realAnalysis)
      zeroSolution := by
  refine ⟨zero_momentum ν, ?_, ?_, zeroRForce_periodic,
    ⟨zeroRForce_vectorSmooth, ?_⟩, ?_⟩
  · intro x t _
    change sum3 realAnalysis
      (fun i => spatialDerivative i (fun _ : RSpace => (0 : ℝ)) x) = 0
    simp [sum3, realAnalysis, dx_const_zero]
  · intro x
    rfl
  · exact ((zero_ambient_analytic 0).2).contDiffOn
  · intro x t _ j
    rfl

theorem zero_hasGlobalSolution (ν : PositiveViscosity realAnalysis) :
    hasGlobalSolution realAnalysis .periodic ν zeroRInitial (zeroForce realAnalysis) :=
  ⟨zeroSolution, zero_global ν⟩

theorem zero_small (ε : ℝ) (hε : 0 < ε) (ν : PositiveViscosity realAnalysis) :
    SmallPeriodicSeed ε ν zeroRInitial := by
  refine {
    smooth := ?_
    solenoidal := admissible_zero.2.1
    periodic := admissible_zero.2.2
    integrableCube := ?_
    smallCube := ?_ }
  · intro i
    change ContDiff ℝ ∞ (fun _ : RSpace => (0 : ℝ))
    exact contDiff_const
  · simp [MeasureTheory.IntegrableOn, zeroRInitial, euclideanNorm3, normSq3]
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
    velocityPeriodic := h.2.2.2.1
    pressurePeriodic := h.2.2.2.2.2 }
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

end Fefferman.ConcreteReal.AdjustedB

set_option autoImplicit false

open MeasureTheory
open scoped ContDiff

namespace Fefferman.ConcreteReal.AdjustedB.ConstantSeed

noncomputable section

def datum (v : RVector) : RInitial := fun _ => v

def flow (v : RVector) : Solution realAnalysis where
  velocity := fun _ _ => v
  pressure := fun _ _ => 0

private theorem dx_const (j : Fin 3) (c : ℝ) :
    spatialDerivative j (fun _ : RSpace => c) = fun _ => 0 := by
  funext x
  change (fderiv ℝ (fun _ : RSpace => c) x) (basisDirection j) = 0
  rw [fderiv_const_apply (𝕜 := ℝ) (x := x) c] <;> rfl

private theorem lap_const (x : RSpace) (c : ℝ) :
    laplacian realAnalysis (fun _ : RSpace => c) x = 0 := by
  change sum3 realAnalysis
    (fun j => spatialDerivative j (spatialDerivative j (fun _ : RSpace => c)) x) = 0
  simp [sum3, realAnalysis, dx_const]

theorem admissible (v : RVector) : admissibleInitial realAnalysis .periodic (datum v) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    change ContDiff ℝ ⊤ (fun _ : RSpace => v i)
    exact contDiff_const
  · intro x
    change sum3 realAnalysis (fun i => spatialDerivative i (fun _ : RSpace => v i) x) = 0
    simp [sum3, realAnalysis, dx_const]
  · intro x j
    rfl

theorem positive_flow (ν : PositiveViscosity realAnalysis) (v : RVector) :
    GlobalPositiveFlow ν (datum v) (flow v) := by
  refine {
    momentum := ?_
    solenoidal := ?_
    initial := ?_
    smoothVelocity := ?_
    analyticVelocity := ?_
    analyticPressure := ?_
    velocityPeriodic := ?_
    pressurePeriodic := ?_ }
  · intro x t _ i
    change timeDerivative (fun _ : ℝ => v i) t +
      sum3 realAnalysis (fun j => v j * spatialDerivative j (fun _ : RSpace => v i) x) =
      ν.val * laplacian realAnalysis (fun _ : RSpace => v i) x +
        -(spatialDerivative i (fun _ : RSpace => (0 : ℝ)) x) + 0
    rw [lap_const x]
    simp [dx_const, timeDerivative, sum3, realAnalysis]
  · intro x t _
    exact (admissible v).2.1 x
  · intro x
    rfl
  · intro i
    exact (contDiff_const : ContDiff ℝ ∞ (fun _ : RSpace × ℝ => v i)).contDiffOn
  · intro i
    exact (contDiff_const : ContDiff ℝ ⊤ (fun _ : RSpace × ℝ => v i)).contDiffOn
  · exact (contDiff_const : ContDiff ℝ ⊤ (fun _ : RSpace × ℝ => (0 : ℝ))).contDiffOn
  · intro x t _ j
    rfl
  · intro x t _ j
    rfl

theorem volume_periodCell : volume periodCell = 1 := by
  simp [periodCell, Real.volume_Icc_pi]

theorem small (ε : ℝ) (ν : PositiveViscosity realAnalysis) (v : RVector)
    (hv : euclideanNorm3 v < ε * ν.val) : SmallPeriodicSeed ε ν (datum v) := by
  refine {
    smooth := ?_
    solenoidal := (admissible v).2.1
    periodic := (admissible v).2.2
    integrableCube := ?_
    smallCube := ?_ }
  · intro i
    exact (contDiff_const : ContDiff ℝ ∞ (fun _ : RSpace => v i))
  · change IntegrableOn (fun _ : RSpace => (euclideanNorm3 v) ^ (3 : ℕ)) periodCell
    exact integrableOn_const (by simp [volume_periodCell])
  · change (∫ _ in periodCell, (euclideanNorm3 v) ^ (3 : ℕ)) < (ε * ν.val) ^ (3 : ℕ)
    rw [setIntegral_const]
    simpa [measureReal_def, volume_periodCell] using
      (pow_lt_pow_left₀ hv (Real.sqrt_nonneg (normSq3 v)) (by decide : (3 : ℕ) ≠ 0))

theorem positive_time_state (ε : ℝ) (ν : PositiveViscosity realAnalysis) (v : RVector)
    (hv : euclideanNorm3 v < ε * ν.val) : PositiveTimeState ε ν (datum v) := by
  exact ⟨datum v, 1, flow v, small ε ν v hv, zero_lt_one, positive_flow ν v, rfl⟩

/-- A nonzero periodic datum and an explicitly witnessed regular solution for every
positive threshold and viscosity. Its first component equals half the threshold. -/
theorem exists_nonzero_positive_time_state (ε : ℝ) (hε : 0 < ε)
    (ν : PositiveViscosity realAnalysis) :
    ∃ u₀ : RInitial, u₀ ≠ zeroRInitial ∧ admissibleInitial realAnalysis .periodic u₀ ∧
      PositiveTimeState ε ν u₀ ∧
      hasGlobalSolution realAnalysis .periodic ν u₀ (zeroForce realAnalysis) := by
  let c : ℝ := (ε * ν.val) / 2
  let v : RVector := ![c, 0, 0]
  have hν : (0 : ℝ) < ν.val := ν.property
  have hc : 0 < c := half_pos (mul_pos hε hν)
  have hnorm : euclideanNorm3 v = c := by
    change Real.sqrt (c * c + 0 * 0 + 0 * 0) = c
    simpa using Real.sqrt_mul_self hc.le
  have hv : euclideanNorm3 v < ε * ν.val := by
    rw [hnorm]
    exact half_lt_self (mul_pos hε hν)
  have hs := positive_time_state ε ν v hv
  refine ⟨datum v, ?_, admissible v, hs, FEF_B_POSITIVE_TIME ε ν _ (admissible v) hs⟩
  intro hzero
  have heq := congrArg (fun f : RInitial => f (0 : RSpace) 0) hzero
  exact hc.ne' (show c = 0 from heq)

end

end Fefferman.ConcreteReal.AdjustedB.ConstantSeed
