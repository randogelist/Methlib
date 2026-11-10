import NSE_NOH

/-!
# NSE_NOH - concrete, independent 2D3C pointwise geometry

These lemmas construct the exact equivalence between x1-independent
THREE-COMPONENT real-valued fields and scalar + TWO-COMPONENT planar fields.
This is an actual geometric edge, not a replacement for the OPEN
2D Navier-Stokes L2 existence and passive-scalar regularity theorems.

Source preparation for the user's external native Windows Lean 4.33.0.
NO LOCAL LEAN EXECUTION. No sorry, axioms or admitted PDE theorems.
-/

set_option autoImplicit false
set_option maxHeartbeats 0

namespace NSE_NOH

noncomputable section

/- A canonical section of the two-coordinate projection x -> (x2,x3). -/
def realEmbedding2 (y : RSpace 2) : RSpace 3 :=
  ![(0 : ℝ), y 0, y 1]

theorem realProjection2_realEmbedding2 (y : RSpace 2) :
    realProjection2 (realEmbedding2 y) = y := by
  funext i
  fin_cases i <;> rfl

theorem realProjection2_update_zero (x : RSpace 3) (r : ℝ) :
    realProjection2 (Function.update x (0 : Fin 3) r) = realProjection2 x := by
  funext i
  fin_cases i <;> simp [realProjection2, Function.update]

theorem realEmbedding2_realProjection2 (x : RSpace 3) :
    realEmbedding2 (realProjection2 x) = Function.update x (0 : Fin 3) 0 := by
  funext i
  fin_cases i <;> simp [realEmbedding2, realProjection2, Function.update]

/- Actual pointwise x1 invariance of the THREE-COMPONENT velocity. -/
def PointwiseX1Invariant (u : ℝ → RSpace 3 → Vector 3) : Prop :=
  ∀ (t : ℝ) (x : RSpace 3) (r : ℝ),
    u t (Function.update x (0 : Fin 3) r) = u t x

/- The scalar pressure has the analogous exact pointwise notion. -/
def PointwiseX1InvariantScalar (p : ℝ → RSpace 3 → ℝ) : Prop :=
  ∀ (t : ℝ) (x : RSpace 3) (r : ℝ),
    p t (Function.update x (0 : Fin 3) r) = p t x

def sliceScalar (u : ℝ → RSpace 3 → Vector 3) : ℝ → RSpace 2 → ℝ :=
  fun t y => u t (realEmbedding2 y) 0

def slicePlanar (u : ℝ → RSpace 3 → Vector 3) : ℝ → RSpace 2 → Vector 2 :=
  fun t y => ![u t (realEmbedding2 y) 1, u t (realEmbedding2 y) 2]

def slicePressure (p : ℝ → RSpace 3 → ℝ) : ℝ → RSpace 2 → ℝ :=
  fun t y => p t (realEmbedding2 y)

/- Every constructed 2D3C lift is x1 invariant by calculation, without
assuming a solution, derivative, L2 representative or a PDE. -/
theorem liftedVelocity_x1_invariant
    (w : ℝ → RSpace 2 → ℝ) (v : ℝ → RSpace 2 → Vector 2) :
    PointwiseX1Invariant (liftedVelocity w v) := by
  intro t x r
  simp only [liftedVelocity, realProjection2_update_zero]

theorem liftedPressure_x1_invariant (q : ℝ → RSpace 2 → ℝ) :
    PointwiseX1InvariantScalar (liftedPressure q) := by
  intro t x r
  simp only [liftedPressure, realProjection2_update_zero]

/- Sections of a lifted field recover EXACTLY its original planar data. -/
theorem sliceScalar_liftedVelocity
    (w : ℝ → RSpace 2 → ℝ) (v : ℝ → RSpace 2 → Vector 2) :
    sliceScalar (liftedVelocity w v) = w := by
  funext t y
  simp [sliceScalar, liftedVelocity, realProjection2_realEmbedding2]

theorem slicePlanar_liftedVelocity
    (w : ℝ → RSpace 2 → ℝ) (v : ℝ → RSpace 2 → Vector 2) :
    slicePlanar (liftedVelocity w v) = v := by
  funext t y i
  fin_cases i <;> simp [slicePlanar, liftedVelocity,
    realProjection2_realEmbedding2]

theorem slicePressure_liftedPressure (q : ℝ → RSpace 2 → ℝ) :
    slicePressure (liftedPressure q) = q := by
  funext t y
  simp [slicePressure, liftedPressure, realProjection2_realEmbedding2]

/- Every pointwise x1-invariant field is EXACTLY the lift of its slices. -/
theorem liftedVelocity_slice_of_invariant
    (u : ℝ → RSpace 3 → Vector 3) (h : PointwiseX1Invariant u) :
    liftedVelocity (sliceScalar u) (slicePlanar u) = u := by
  funext t x
  calc
    liftedVelocity (sliceScalar u) (slicePlanar u) t x =
        u t (realEmbedding2 (realProjection2 x)) := by
          funext i
          fin_cases i <;> rfl
    _ = u t (Function.update x (0 : Fin 3) 0) := by
          rw [realEmbedding2_realProjection2]
    _ = u t x := h t x 0

theorem liftedPressure_slice_of_invariant
    (p : ℝ → RSpace 3 → ℝ) (h : PointwiseX1InvariantScalar p) :
    liftedPressure (slicePressure p) = p := by
  funext t x
  change p t (realEmbedding2 (realProjection2 x)) = p t x
  rw [realEmbedding2_realProjection2]
  exact h t x 0

/- A true equivalence of mathematical classes at the pointwise level.
This DOES NOT claim equivalence of L2 equivalence classes, for which
measure-preservation and almost-everywhere representative theorems
are still required. -/
theorem pointwiseX1Invariant_iff_exists_lift
    (u : ℝ → RSpace 3 → Vector 3) :
    PointwiseX1Invariant u ↔
      ∃ (w : ℝ → RSpace 2 → ℝ) (v : ℝ → RSpace 2 → Vector 2),
        liftedVelocity w v = u := by
  constructor
  · intro h
    exact ⟨sliceScalar u, slicePlanar u,
      liftedVelocity_slice_of_invariant u h⟩
  · rintro ⟨w, v, h⟩
    rw [← h]
    exact liftedVelocity_x1_invariant w v

theorem liftedVelocity_injective_components
    {w₁ w₂ : ℝ → RSpace 2 → ℝ}
    {v₁ v₂ : ℝ → RSpace 2 → Vector 2}
    (h : liftedVelocity w₁ v₁ = liftedVelocity w₂ v₂) :
    w₁ = w₂ ∧ v₁ = v₂ := by
  constructor
  · have hs := congrArg sliceScalar h
    simpa only [sliceScalar_liftedVelocity] using hs
  · have hp := congrArg slicePlanar h
    simpa only [slicePlanar_liftedVelocity] using hp

/- Exact Fourier frequency sublattice: (k1=0) in Z^3 is canonically Z^2.
This elementary edge is suited for an eventual L2 Fourier-support bridge. -/
def modeEmbedding2 (k : Fin 2 → ℤ) : Fin 3 → ℤ :=
  ![(0 : ℤ), k 0, k 1]

def modeProjection2 (k : Fin 3 → ℤ) : Fin 2 → ℤ :=
  fun i => k (Fin.succ i)

theorem modeProjection2_modeEmbedding2 (k : Fin 2 → ℤ) :
    modeProjection2 (modeEmbedding2 k) = k := by
  funext i
  fin_cases i <;> rfl

theorem modeEmbedding2_modeProjection2
    (k : Fin 3 → ℤ) (hk : k 0 = 0) :
    modeEmbedding2 (modeProjection2 k) = k := by
  funext i
  fin_cases i <;> simp [modeEmbedding2, modeProjection2, hk]

theorem x1zero_mode_iff_exists_planar_mode (k : Fin 3 → ℤ) :
    k 0 = 0 ↔ ∃ l : Fin 2 → ℤ, modeEmbedding2 l = k := by
  constructor
  · intro hk
    exact ⟨modeProjection2 k, modeEmbedding2_modeProjection2 k hk⟩
  · rintro ⟨l, rfl⟩
    rfl

theorem modeEmbedding2_injective : Function.Injective modeEmbedding2 := by
  intro k l h
  have hp := congrArg modeProjection2 h
  simpa only [modeProjection2_modeEmbedding2] using hp

/- The geometrically constrained lift packages only what remains open:
construct the ACTUAL 3D PDE flow with exact lifted velocity, pressure,
strong L2 trace, periodicity, energy equality and weak trace invariance.
Positive-time pointwise invariance is no longer an external premise. -/
structure GeometricLift (ν : ℝ) (a : L2Vector 3)
    {v₀ : L2Vector 2} {w₀ : L2Scalar2}
    (v : GlobalNSEFlow 2 ν v₀) (w : PassiveFlow ν v w₀) : Type where
  flow : GlobalNSEFlow 3 ν a
  velocity_eq : flow.velocity = liftedVelocity w.scalar v.velocity
  pressure_eq : flow.pressure = liftedPressure v.pressure
  invariantTrace : ∀ t : NNReal, WeakX1Invariant (flow.path t)

/- This term construction DISCHARGES two previously assumed geometry
fields of NOHSolution by the actual pointwise lift theorems. -/
def GeometricLift.toNOHSolution
    {ν : ℝ} {a : L2Vector 3} {v₀ : L2Vector 2} {w₀ : L2Scalar2}
    {v : GlobalNSEFlow 2 ν v₀} {w : PassiveFlow ν v w₀}
    (L : GeometricLift ν a v w) : NOHSolution ν a where
  flow := L.flow
  invariantTrace := L.invariantTrace
  invariantPositiveVelocity := by
    intro t _ht x r
    change L.flow.velocity t (Function.update x (0 : Fin 3) r) =
      L.flow.velocity t x
    rw [L.velocity_eq]
    exact liftedVelocity_x1_invariant w.scalar v.velocity t x r
  invariantPositivePressure := by
    intro t _ht x r
    change L.flow.pressure t (Function.update x (0 : Fin 3) r) =
      L.flow.pressure t x
    rw [L.pressure_eq]
    exact liftedPressure_x1_invariant v.pressure t x r

/- Smaller non-circular interface: lifted positive-time invariance
is PROVED ABOVE and is not supplied again by this structure. The
analytical PDE input for the lifted GlobalNSEFlow remains explicit. -/
structure GeometryPorts where
  invariantSplit : ∀ (a : L2Vector 3),
    WeakDivergenceFree 3 a → WeakX1Invariant a → SplitData a
  planarGlobalSmooth : ∀ (ν : ℝ), 0 < ν →
    ∀ {a : L2Vector 3} (d : SplitData a), GlobalNSEFlow 2 ν d.v₀
  passiveGlobalSmooth : ∀ (ν : ℝ), 0 < ν →
    ∀ {a : L2Vector 3} (d : SplitData a)
      (v : GlobalNSEFlow 2 ν d.v₀), PassiveFlow ν v d.w₀
  reconstructLift : ∀ (ν : ℝ), 0 < ν →
    ∀ {a : L2Vector 3} (d : SplitData a)
      (v : GlobalNSEFlow 2 ν d.v₀)
      (w : PassiveFlow ν v d.w₀), GeometricLift ν a v w

def GeometryPorts.toAnalyticPorts (P : GeometryPorts) : AnalyticPorts where
  invariantSplit := P.invariantSplit
  planarGlobalSmooth := P.planarGlobalSmooth
  passiveGlobalSmooth := P.passiveGlobalSmooth
  reconstruct3D := by
    intro ν hν a d v w
    exact (P.reconstructLift ν hν d v w).toNOHSolution

theorem from_geometry_ports (P : GeometryPorts) : NSE_NOH := by
  exact from_analytic_ports P.toAnalyticPorts

end
end NSE_NOH

/- The exact unconditional root remains a Prop, not a proved theorem. -/
#check NSE_NOH.from_geometry_ports
#print axioms NSE_NOH.from_geometry_ports
#check NSE_NOH.pointwiseX1Invariant_iff_exists_lift
#print axioms NSE_NOH.pointwiseX1Invariant_iff_exists_lift
#check NSE_NOH.GeometricLift.toNOHSolution
#print axioms NSE_NOH.GeometricLift.toNOHSolution
