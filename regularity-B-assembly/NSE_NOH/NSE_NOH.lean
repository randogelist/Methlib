import Mathlib

/-!
# NSE_NOH: exact root proposition and conditional 2D3C assembly

This is a source-only preparation for external Lean 4.33.0 or 4.34.0-rc1.
The root `NSE_NOH` below is a proposition, not an established theorem.
`from_analytic_ports` proves a dependency-explicit conditional chain.
Every analytic PDE port must receive an independent proof before the
unconditional root can be established. No local compiler was executed.
-/

set_option autoImplicit false
set_option maxHeartbeats 0

open MeasureTheory
open scoped ENNReal

namespace NSE_NOH

noncomputable section

/- The actual normalized flat torus, rather than a synthetic data type. -/
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

abbrev Torus (n : ℕ) := UnitAddTorus (Fin n)
abbrev RSpace (n : ℕ) := Fin n → ℝ
abbrev Vector (n : ℕ) := Fin n → ℝ
abbrev L2Vector (n : ℕ) := Lp (Vector n) (2 : ℝ≥0∞) (volume : Measure (Torus n))
abbrev L2Scalar2 := Lp ℝ (2 : ℝ≥0∞) (volume : Measure (Torus 2))

/- Pull a real-coordinate point back to the unit torus. -/
def realToTorus (n : ℕ) (x : RSpace n) : Torus n :=
  fun i => (x i : UnitAddCircle)

def cube (n : ℕ) : Set (RSpace n) :=
  {x | ∀ i : Fin n, (0 : ℝ) ≤ x i ∧ x i ≤ 1}

def shiftedCoordinate (n : ℕ) (x : RSpace n) (j : Fin n) : RSpace n :=
  fun i => x i + (if i = j then (1 : ℝ) else 0)

def UnitPeriodic (n : ℕ) (f : RSpace n → ℝ) : Prop :=
  ∀ (x : RSpace n) (j : Fin n), f (shiftedCoordinate n x j) = f x

/- Spatial distributional differentiation is encoded by the weak testing
identity against all smooth periodic scalar/vector tests. -/
def coordinateDerivative (n : ℕ) (i : Fin n) (f : RSpace n → ℝ)
    (x : RSpace n) : ℝ :=
  (fderiv ℝ f x) (fun j => if j = i then (1 : ℝ) else 0)

def spatialLaplacian (n : ℕ) (f : RSpace n → ℝ) (x : RSpace n) : ℝ :=
  ∑ j : Fin n, coordinateDerivative n j (coordinateDerivative n j f) x

def WeakDivergenceFree (n : ℕ) (a : L2Vector n) : Prop :=
  ∀ (test : RSpace n → ℝ),
    ContDiff ℝ ⊤ test → UnitPeriodic n test →
    (∫ x in cube n,
      ∑ i : Fin n,
        (a (realToTorus n x) i) * coordinateDerivative n i test x) = 0

/- `x1` is coordinate 0. This is the exact vector-valued distributional
condition ∂_(x1) a = 0 tested against arbitrary smooth periodic vectors. -/
def WeakX1Invariant (a : L2Vector 3) : Prop :=
  ∀ (test : RSpace 3 → Vector 3),
    (∀ i : Fin 3, ContDiff ℝ ⊤ (fun x => test x i)) →
    (∀ i : Fin 3, UnitPeriodic 3 (fun x => test x i)) →
    (∫ x in cube 3,
      ∑ i : Fin 3,
        (a (realToTorus 3 x) i) *
          coordinateDerivative 3 0 (fun y => test y i) x) = 0

/- The energy mass is the physical Euclidean sum of component squares.
This avoids accidentally substituting the default Pi supremum norm. -/
def mass (n : ℕ) (a : L2Vector n) : ℝ :=
  ∫ x : Torus n, ∑ i : Fin n, (a x i) ^ (2 : ℕ)

def scalarMass (a : L2Scalar2) : ℝ :=
  ∫ x : Torus 2, (a x) ^ (2 : ℕ)

def vectorDirichlet (n : ℕ) (u : ℝ → RSpace n → Vector n) (t : ℝ) : ℝ :=
  ∫ x in cube n,
    ∑ i : Fin n, ∑ j : Fin n,
      (coordinateDerivative n j (fun y => u t y i) x) ^ (2 : ℕ)

def scalarDirichlet (w : ℝ → RSpace 2 → ℝ) (t : ℝ) : ℝ :=
  ∫ x in cube 2,
    ∑ j : Fin 2, (coordinateDerivative 2 j (w t) x) ^ (2 : ℕ)

/- A positive-time smooth representative must agree with the L2 equivalence
class almost everywhere on the unit cell at each positive time. -/
def MatchesL2 (n : ℕ) (a : L2Vector n)
    (u : ℝ → RSpace n → Vector n) (t : ℝ) : Prop :=
  ∀ᵐ x ∂((volume : Measure (RSpace n)).restrict (cube n)),
    a (realToTorus n x) = u t x

def MatchesScalarL2 (a : L2Scalar2)
    (w : ℝ → RSpace 2 → ℝ) (t : ℝ) : Prop :=
  ∀ᵐ x ∂((volume : Measure (RSpace 2)).restrict (cube 2)),
    a (realToTorus 2 x) = w t x

def SmoothPositiveVector (n : ℕ) (u : ℝ → RSpace n → Vector n) : Prop :=
  ∀ i : Fin n,
    ContDiffOn ℝ ⊤
      (fun z : ℝ × RSpace n => u z.1 z.2 i)
      {z | 0 < z.1}

def SmoothPositiveScalar (n : ℕ) (p : ℝ → RSpace n → ℝ) : Prop :=
  ContDiffOn ℝ ⊤
    (fun z : ℝ × RSpace n => p z.1 z.2)
    {z | 0 < z.1}

def PeriodicPositiveVector (n : ℕ) (u : ℝ → RSpace n → Vector n) : Prop :=
  ∀ (t : ℝ), 0 < t → ∀ i : Fin n, UnitPeriodic n (fun x => u t x i)

def PeriodicPositiveScalar (n : ℕ) (p : ℝ → RSpace n → ℝ) : Prop :=
  ∀ (t : ℝ), 0 < t → UnitPeriodic n (p t)

/- The actual classical unforced n-dimensional NSE equation at positive
times, using ordinary derivatives of the real periodic lift. -/
def ClassicalNSE (n : ℕ) (ν : ℝ)
    (u : ℝ → RSpace n → Vector n)
    (p : ℝ → RSpace n → ℝ) : Prop :=
  ∀ (t : ℝ), 0 < t → ∀ x : RSpace n,
    (∀ i : Fin n,
       deriv (fun s : ℝ => u s x i) t +
           (∑ j : Fin n,
             u t x j * coordinateDerivative n j (fun y => u t y i) x) +
           coordinateDerivative n i (p t) x =
           ν * spatialLaplacian n (fun y => u t y i) x) ∧
    (∑ i : Fin n, coordinateDerivative n i (fun y => u t y i) x) = 0

/- This record spells out the positive-time PDE and the strong L2 boundary
trace. It does not make existence an automatic consequence of definition. -/
structure GlobalNSEFlow (n : ℕ) (ν : ℝ) (a : L2Vector n) where
  path : NNReal → L2Vector n
  velocity : ℝ → RSpace n → Vector n
  pressure : ℝ → RSpace n → ℝ
  continuousL2 : Continuous path
  initialL2 : path 0 = a
  divergenceFreeL2 : ∀ t : NNReal, WeakDivergenceFree n (path t)
  positiveAgreement : ∀ (t : ℝ) (ht : 0 < t),
    MatchesL2 n (path ⟨t, ht.le⟩) velocity t
  positiveSmoothVelocity : SmoothPositiveVector n velocity
  positiveSmoothPressure : SmoothPositiveScalar n pressure
  periodicVelocity : PeriodicPositiveVector n velocity
  periodicPressure : PeriodicPositiveScalar n pressure
  equations : ClassicalNSE n ν velocity pressure
  gradientLocallyIntegrable : ∀ (T : ℝ), 0 < T →
    IntegrableOn (vectorDirichlet n velocity) (Set.Ioc 0 T)
  energyEquality : ∀ t : NNReal,
    mass n (path t) +
        2 * ν * (∫ s in (0 : ℝ)..(t : ℝ), vectorDirichlet n velocity s)
          = mass n a

/- A scalar L2 solution advected by the ACTUAL 2D velocity. -/
def ClassicalPassiveScalar (ν : ℝ)
    (v : ℝ → RSpace 2 → Vector 2)
    (w : ℝ → RSpace 2 → ℝ) : Prop :=
  ∀ (t : ℝ), 0 < t → ∀ x : RSpace 2,
    deriv (fun s : ℝ => w s x) t +
       (∑ j : Fin 2, v t x j * coordinateDerivative 2 j (w t) x)
          = ν * spatialLaplacian 2 (w t) x

structure PassiveFlow (ν : ℝ) {v₀ : L2Vector 2}
    (v : GlobalNSEFlow 2 ν v₀) (w₀ : L2Scalar2) where
  path : NNReal → L2Scalar2
  scalar : ℝ → RSpace 2 → ℝ
  continuousL2 : Continuous path
  initialL2 : path 0 = w₀
  positiveAgreement : ∀ (t : ℝ) (ht : 0 < t),
    MatchesScalarL2 (path ⟨t, ht.le⟩) scalar t
  positiveSmooth : SmoothPositiveScalar 2 scalar
  periodic : PeriodicPositiveScalar 2 scalar
  equation : ClassicalPassiveScalar ν v.velocity scalar
  gradientLocallyIntegrable : ∀ (T : ℝ), 0 < T →
    IntegrableOn (scalarDirichlet scalar) (Set.Ioc 0 T)
  energyEquality : ∀ t : NNReal,
    scalarMass (path t) +
      2 * ν * (∫ s in (0 : ℝ)..(t : ℝ), scalarDirichlet scalar s)
        = scalarMass w₀

/- Exact reconstruction from two-dimensional coordinates. -/
def realProjection2 (x : RSpace 3) : RSpace 2 :=
  fun i => x (Fin.succ i)

def torusProjection2 (x : Torus 3) : Torus 2 :=
  fun i => x (Fin.succ i)

def liftedVelocity (w : ℝ → RSpace 2 → ℝ)
    (v : ℝ → RSpace 2 → Vector 2) : ℝ → RSpace 3 → Vector 3 :=
  fun t x => ![w t (realProjection2 x),
               v t (realProjection2 x) 0,
               v t (realProjection2 x) 1]

def liftedPressure (q : ℝ → RSpace 2 → ℝ) : ℝ → RSpace 3 → ℝ :=
  fun t x => q t (realProjection2 x)

/- The first independent coordinate endpoint; it does not prove that
any nonlinear 2D global solution exists. -/
theorem liftedVelocity_component_zero
    (w : ℝ → RSpace 2 → ℝ) (v : ℝ → RSpace 2 → Vector 2)
    (t : ℝ) (x : RSpace 3) :
    liftedVelocity w v t x 0 = w t (realProjection2 x) := by
  rfl

theorem liftedVelocity_component_one
    (w : ℝ → RSpace 2 → ℝ) (v : ℝ → RSpace 2 → Vector 2)
    (t : ℝ) (x : RSpace 3) :
    liftedVelocity w v t x 1 = v t (realProjection2 x) 0 := by
  rfl

theorem liftedVelocity_component_two
    (w : ℝ → RSpace 2 → ℝ) (v : ℝ → RSpace 2 → Vector 2)
    (t : ℝ) (x : RSpace 3) :
    liftedVelocity w v t x 2 = v t (realProjection2 x) 1 := by
  rfl

/- Each invariant datum is decomposed AS AN L2 equivalence class, with
componentwise almost-everywhere equality and correct energy mass. -/
structure SplitData (a : L2Vector 3) where
  w₀ : L2Scalar2
  v₀ : L2Vector 2
  planarDivergenceFree : WeakDivergenceFree 2 v₀
  equalityAE :
    ∀ᵐ x : Torus 3 ∂(volume : Measure (Torus 3)),
      a x = ![w₀ (torusProjection2 x),
               v₀ (torusProjection2 x) 0,
               v₀ (torusProjection2 x) 1]
  massDecomposition : mass 3 a = scalarMass w₀ + mass 2 v₀

structure NOHSolution (ν : ℝ) (a : L2Vector 3) where
  flow : GlobalNSEFlow 3 ν a
  invariantTrace : ∀ t : NNReal, WeakX1Invariant (flow.path t)
  invariantPositiveVelocity :
    ∀ (t : ℝ), 0 < t → ∀ (x : RSpace 3) (r : ℝ),
      flow.velocity t (Function.update x (0 : Fin 3) r) = flow.velocity t x
  invariantPositivePressure :
    ∀ (t : ℝ), 0 < t → ∀ (x : RSpace 3) (r : ℝ),
      flow.pressure t (Function.update x (0 : Fin 3) r) = flow.pressure t x

/- FROZEN UNCONDITIONAL ROOT: this is a DEFINITION OF A GOAL, not a theorem. -/
def NSE_NOH : Prop :=
  ∀ (ν : ℝ), 0 < ν →
    ∀ (a : L2Vector 3), WeakDivergenceFree 3 a → WeakX1Invariant a →
      Nonempty (NOHSolution ν a)

/- These are the independent UNRESOLVED analytic/geometry endpoints.
They are parameters of the conditional composition theorem below.
N02: actual L2-invariant decomposition.
N04+N05: global 2D L2 NSE and smoothing.
N06+N07: passive scalar L2 evolution and smoothing.
N03+N08+N09: concrete three-dimensional lift, trace and energy.
No parameter is supplied by a proof in this package. -/
structure AnalyticPorts where
  invariantSplit : ∀ (a : L2Vector 3),
    WeakDivergenceFree 3 a → WeakX1Invariant a → SplitData a
  planarGlobalSmooth : ∀ (ν : ℝ), 0 < ν →
    ∀ {a : L2Vector 3} (d : SplitData a), GlobalNSEFlow 2 ν d.v₀
  passiveGlobalSmooth : ∀ (ν : ℝ), 0 < ν →
    ∀ {a : L2Vector 3} (d : SplitData a)
      (v : GlobalNSEFlow 2 ν d.v₀), PassiveFlow ν v d.w₀
  reconstruct3D : ∀ (ν : ℝ), 0 < ν →
    ∀ {a : L2Vector 3} (d : SplitData a)
      (v : GlobalNSEFlow 2 ν d.v₀)
      (_w : PassiveFlow ν v d.w₀), NOHSolution ν a

/- Genuine term-level conditional assembly of the unchanged conclusion.
The full unconditional root still requires a construction of `AnalyticPorts`.
No assumption in this theorem may be hidden in the conclusion. -/
theorem from_analytic_ports (P : AnalyticPorts) : NSE_NOH := by
  intro ν hν a hσ h₁
  let d : SplitData a := P.invariantSplit a hσ h₁
  let v : GlobalNSEFlow 2 ν d.v₀ := P.planarGlobalSmooth ν hν d
  let w : PassiveFlow ν v d.w₀ := P.passiveGlobalSmooth ν hν d v
  exact ⟨P.reconstruct3D ν hν d v w⟩

/- A distinct endpoint for future proof of uniqueness within the invariant
energy solution class; unrestricted three-dimensional weak uniqueness
is NOT a conclusion of the frozen root. -/
def InvariantUniqueness : Prop :=
  ∀ (ν : ℝ) (_hν : 0 < ν) (a : L2Vector 3)
    (u v : NOHSolution ν a),
      u.flow.path = v.flow.path

end
end NSE_NOH

/- The output of these commands belongs to the EXTERNAL compiler log.
An audit of `from_analytic_ports` cannot discharge its `AnalyticPorts`
argument. `NSE_NOH.NSE_NOH` is a proposition, not a proved declaration. -/
#check NSE_NOH.NSE_NOH
#print NSE_NOH.NSE_NOH
#check NSE_NOH.from_analytic_ports
#print axioms NSE_NOH.from_analytic_ports
#check NSE_NOH.InvariantUniqueness
