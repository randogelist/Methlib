import RH_HilbertLimit.ZeroBudgetFirstMoment
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

set_option autoImplicit false

namespace Tail16Frontier

/-- Finite rational coordinates. These fields carry no analytic proof. -/
structure MomentData where
  centers : List ℚ
  radii : List ℚ
deriving Repr, DecidableEq

/-- Total, Lean-4.33-compatible coordinate lookup. Shape checks exclude missing entries. -/
def rationalAt : List ℚ → Nat → ℚ
  | [], _ => 0
  | q :: _, 0 => q
  | _ :: qs, n + 1 => rationalAt qs n

namespace MomentData

def center (d : MomentData) (k : Nat) : ℚ := rationalAt d.centers k

def radius (d : MomentData) (k : Nat) : ℚ := rationalAt d.radii k

/-- Structural validation only. This Boolean does not establish actual-moment meaning. -/
def shapeCheck (d : MomentData) (N : Nat) : Bool :=
  decide (d.centers.length = N + 1 ∧ d.radii.length = N + 1)

/-- The exact actual-ξ meaning of the supplied finite rational coordinates. -/
def Encloses (d : MomentData) (N : Nat) : Prop :=
  ∀ k : Nat, k ≤ N →
    |RH_HilbertLimit.actualNormalizedMoment k - (d.center k : ℝ)|
      ≤ (d.radius k : ℝ)

theorem shapeCheck_iff (d : MomentData) (N : Nat) :
    d.shapeCheck N = true ↔
      d.centers.length = N + 1 ∧ d.radii.length = N + 1 := by
  simp [shapeCheck]

theorem encloses_mono {d : MomentData} {M N : Nat}
    (h : d.Encloses N) (hMN : M ≤ N) : d.Encloses M := by
  intro k hk
  exact h k (le_trans hk hMN)

theorem radius_nonneg_of_encloses {d : MomentData} {N k : Nat}
    (h : d.Encloses N) (hk : k ≤ N) : 0 ≤ d.radius k := by
  have hr : (0 : ℝ) ≤ (d.radius k : ℝ) :=
    le_trans (abs_nonneg _) (h k hk)
  exact_mod_cast hr

theorem lower_of_encloses {d : MomentData} {N k : Nat}
    (h : d.Encloses N) (hk : k ≤ N) :
    (d.center k : ℝ) - (d.radius k : ℝ) ≤
      RH_HilbertLimit.actualNormalizedMoment k := by
  have hl := (abs_le.mp (h k hk)).1
  linarith

theorem upper_of_encloses {d : MomentData} {N k : Nat}
    (h : d.Encloses N) (hk : k ≤ N) :
    RH_HilbertLimit.actualNormalizedMoment k ≤
      (d.center k : ℝ) + (d.radius k : ℝ) := by
  have hu := (abs_le.mp (h k hk)).2
  linarith

end MomentData

/-- Root alias for structural validation. -/
def shapeCheck (d : MomentData) (N : Nat) : Bool := d.shapeCheck N

/--
Typed output of native proof-carrying moment admission.

`encloses` must be supplied by a checked Lean proof. It is not produced by
`shapeCheck` and is not evidence that a raw numerical source checker exists.
-/
structure AdmittedMoments where
  degree : Nat
  data : MomentData
  shape : data.shapeCheck degree = true
  encloses : data.Encloses degree

def admitMoments (d : MomentData) (N : Nat)
    (hshape : d.shapeCheck N = true)
    (hactual : d.Encloses N) : AdmittedMoments :=
  ⟨N, d, hshape, hactual⟩

theorem admittedMoments_sound (a : AdmittedMoments) :
    a.data.Encloses a.degree := a.encloses

/-- Exact zeroth-moment control; no RH premise. -/
def zeroMomentData : MomentData :=
  { centers := [1], radii := [0] }

theorem zeroMomentData_shape : zeroMomentData.shapeCheck 0 = true := by
  decide

theorem zeroMomentData_encloses : zeroMomentData.Encloses 0 := by
  intro k hk
  have hk0 : k = 0 := by omega
  subst k
  simp [zeroMomentData, MomentData.center, MomentData.radius, rationalAt,
    RH_HilbertLimit.actualNormalizedMoment_zero_unconditional]

/-- A coarse but actual first-moment control: u₀=1 and 0≤u₁≤1. -/
def firstMomentData : MomentData :=
  { centers := [1, 1 / 2], radii := [0, 1 / 2] }

theorem firstMomentData_shape : firstMomentData.shapeCheck 1 = true := by
  decide

theorem firstMomentData_encloses : firstMomentData.Encloses 1 := by
  intro k hk
  have hkcases : k = 0 ∨ k = 1 := by omega
  rcases hkcases with rfl | rfl
  · simp [firstMomentData, MomentData.center, MomentData.radius, rationalAt,
      RH_HilbertLimit.actualNormalizedMoment_zero_unconditional]
  · have hlo := RH_HilbertLimit.actualNormalizedMoment_one_nonneg
    have hhi := RH_HilbertLimit.actualNormalizedMoment_one_le_one
    norm_num [firstMomentData, MomentData.center, MomentData.radius,
      rationalAt, abs_le]
    constructor <;> linarith

def admittedZeroMoments : AdmittedMoments :=
  admitMoments zeroMomentData 0 zeroMomentData_shape zeroMomentData_encloses

def admittedFirstMoments : AdmittedMoments :=
  admitMoments firstMomentData 1 firstMomentData_shape firstMomentData_encloses

end Tail16Frontier
