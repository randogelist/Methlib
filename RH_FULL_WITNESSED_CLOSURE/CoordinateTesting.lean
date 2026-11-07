import CoordinateData

/-!
# Concrete finite coordinate testing

SCOPE=FINITE_INTEGER_AND_RATIONAL_CONDITIONS_ONLY
STATUS=A_TIER_CANDIDATE
ACTUAL_XI_ANALYTIC_SOUNDNESS=NOT_ESTABLISHED

The input is the existing data-only `RawCert`. The checker is fully concrete;
it has no checker, soundness, or analytic-proof parameter. All comparisons
use integers and positive natural-number denominators.

Acceptance establishes exactly `CoordinateWellFormed`. In particular, the
advertised G2/G3 bounds are only rational labels: no statement identifies
them with bounds on `actualG2` or `actualG3`. Every `proofData` field is
retained as opaque data and is not analytically verified by this module.

The positive example demonstrates finite-condition acceptance only. It is
not an RH witness. This module does not construct `ClosedSystem`.
-/

set_option autoImplicit false

namespace RHFullWitnessedClosure.CoordinateTesting

/-- Integer cross multiplication; the caller separately checks denominators. -/
def ratLE (a b : ExactRat) : Prop :=
  a.numerator * (b.denominator : Int) ≤
    b.numerator * (a.denominator : Int)

instance (a b : ExactRat) : Decidable (ratLE a b) := by
  unfold ratLE
  infer_instance

/-- Strict integer cross multiplication. -/
def ratLT (a b : ExactRat) : Prop :=
  a.numerator * (b.denominator : Int) <
    b.numerator * (a.denominator : Int)

instance (a b : ExactRat) : Decidable (ratLT a b) := by
  unfold ratLT
  infer_instance

def zeroRat : ExactRat := ⟨0, 1⟩

def oneRat : ExactRat := ⟨1, 1⟩

/-- Finite conditions on the single advertised compact cell. -/
def CellFiniteConditions (split : ExactRat) (c : CellCert) : Prop :=
  0 < c.left.denominator ∧
  0 < c.right.denominator ∧
  0 < c.g2Lower.denominator ∧
  0 < c.g2Upper.denominator ∧
  0 < c.g3Lower.denominator ∧
  0 < c.g3Upper.denominator ∧
  ratLE c.left c.right ∧
  ratLE c.left split ∧
  ratLE oneRat c.right ∧
  ratLE c.g2Lower c.g2Upper ∧
  ratLE c.g3Lower c.g3Upper ∧
  (ratLT c.g2Upper zeroRat ∨
    ratLT zeroRat c.g2Lower ∨
    ratLT zeroRat c.g3Lower)

instance (split : ExactRat) (c : CellCert) :
    Decidable (CellFiniteConditions split c) := by
  unfold CellFiniteConditions
  infer_instance

/-- Exactly one outer cell; its interval covers the rational range [split,1]. -/
def SingleCellFiniteConditions (split : ExactRat) (cells : List CellCert) : Prop :=
  match cells with
  | [cell] => CellFiniteConditions split cell
  | _ => False

instance (split : ExactRat) (cells : List CellCert) :
    Decidable (SingleCellFiniteConditions split cells) := by
  cases cells with
  | nil =>
      change Decidable False
      infer_instance
  | cons cell rest =>
      cases rest with
      | nil =>
          change Decidable (CellFiniteConditions split cell)
          infer_instance
      | cons next tail =>
          change Decidable False
          infer_instance

/--
Exact finite specification. Positive denominators prevent the totalized
real-division convention from silently accepting a zero denominator.
-/
def CoordinateWellFormed (w : RawCert) : Prop :=
  0 < w.spectralCutoff ∧
  0 < w.etaSplit.denominator ∧
  0 < w.nearCert.splitPoint.denominator ∧
  ratLT zeroRat w.etaSplit ∧
  ratLE w.etaSplit oneRat ∧
  w.nearCert.splitPoint = w.etaSplit ∧
  w.tailCert.cutoff = w.spectralCutoff ∧
  SingleCellFiniteConditions w.etaSplit w.cells

instance (w : RawCert) : Decidable (CoordinateWellFormed w) := by
  unfold CoordinateWellFormed
  infer_instance

/-- Concrete terminating test of the finite specification, with no proof input. -/
def coordinateCheck (w : RawCert) : Bool :=
  decide (CoordinateWellFormed w)

/-- Exact reflection; this conclusion contains no actual-xi assertion. -/
theorem coordinateCheck_iff (w : RawCert) :
    coordinateCheck w = true ↔ CoordinateWellFormed w := by
  simp [coordinateCheck]

theorem coordinateCheck_sound (w : RawCert)
    (hAccepted : coordinateCheck w = true) :
    CoordinateWellFormed w :=
  (coordinateCheck_iff w).mp hAccepted

/-- The admitted subtype contains precisely the finite specification. -/
abbrev AdmittedCoordinate :=
  {w : RawCert // CoordinateWellFormed w}

def admitCoordinate (w : RawCert)
    (hAccepted : coordinateCheck w = true) :
    AdmittedCoordinate :=
  ⟨w, coordinateCheck_sound w hAccepted⟩

theorem admitted_coordinate (w : RawCert)
    (hAccepted : coordinateCheck w = true) :
    (admitCoordinate w hAccepted).val = w :=
  rfl

/-- The singleton-cell condition is a finite arithmetic consequence only. -/
theorem accepted_singleCell (w : RawCert)
    (hAccepted : coordinateCheck w = true) :
    SingleCellFiniteConditions w.etaSplit w.cells := by
  have h := coordinateCheck_sound w hAccepted
  exact h.2.2.2.2.2.2.2

def halfRat : ExactRat := ⟨1, 2⟩

def exampleCell : CellCert where
  left := halfRat
  right := oneRat
  g2Lower := ⟨-1, 1⟩
  g2Upper := oneRat
  g3Lower := oneRat
  g3Upper := ⟨2, 1⟩
  proofData := [0]

/-- Accepted finite labels; opaque payload [0] carries no analytic evidence. -/
def exampleFinitePass : RawCert where
  spectralCutoff := 16
  etaSplit := halfRat
  nearCert := { splitPoint := halfRat, proofData := [0] }
  cells := [exampleCell]
  tailCert := { cutoff := 16, proofData := [0] }

def exampleBadDenominator : RawCert :=
  { exampleFinitePass with
    etaSplit := ⟨1, 0⟩
    nearCert := { splitPoint := ⟨1, 0⟩, proofData := [0] } }

def exampleCoverageGap : RawCert :=
  { exampleFinitePass with
    cells := [{ exampleCell with left := oneRat }] }

def exampleMissingCoverage : RawCert :=
  { exampleFinitePass with cells := [] }

def exampleCutoffMismatch : RawCert :=
  { exampleFinitePass with
    tailCert := { cutoff := 17, proofData := [0] } }

def exampleBadInequality : RawCert :=
  { exampleFinitePass with
    cells := [{ exampleCell with g2Lower := ⟨2, 1⟩ }] }

def exampleMissingSignAlternative : RawCert :=
  { exampleFinitePass with
    cells := [{ exampleCell with
      g3Lower := ⟨-2, 1⟩
      g3Upper := ⟨-1, 1⟩ }] }

theorem exampleFinitePass_accepted :
    coordinateCheck exampleFinitePass = true := by
  decide

theorem exampleBadDenominator_rejected :
    coordinateCheck exampleBadDenominator = false := by
  decide

theorem exampleCoverageGap_rejected :
    coordinateCheck exampleCoverageGap = false := by
  decide

theorem exampleMissingCoverage_rejected :
    coordinateCheck exampleMissingCoverage = false := by
  decide

theorem exampleCutoffMismatch_rejected :
    coordinateCheck exampleCutoffMismatch = false := by
  decide

theorem exampleBadInequality_rejected :
    coordinateCheck exampleBadInequality = false := by
  decide

theorem exampleMissingSignAlternative_rejected :
    coordinateCheck exampleMissingSignAlternative = false := by
  decide

#check coordinateCheck_iff
#check coordinateCheck_sound
#check admitted_coordinate
#check accepted_singleCell
#check exampleFinitePass_accepted
#check exampleBadDenominator_rejected
#check exampleCoverageGap_rejected
#check exampleMissingCoverage_rejected
#check exampleCutoffMismatch_rejected
#check exampleBadInequality_rejected
#check exampleMissingSignAlternative_rejected

#print axioms RHFullWitnessedClosure.CoordinateTesting.coordinateCheck_iff
#print axioms RHFullWitnessedClosure.CoordinateTesting.coordinateCheck_sound
#print axioms RHFullWitnessedClosure.CoordinateTesting.admitted_coordinate
#print axioms RHFullWitnessedClosure.CoordinateTesting.accepted_singleCell
#print axioms RHFullWitnessedClosure.CoordinateTesting.exampleFinitePass_accepted
#print axioms RHFullWitnessedClosure.CoordinateTesting.exampleBadDenominator_rejected
#print axioms RHFullWitnessedClosure.CoordinateTesting.exampleCoverageGap_rejected
#print axioms RHFullWitnessedClosure.CoordinateTesting.exampleMissingCoverage_rejected
#print axioms RHFullWitnessedClosure.CoordinateTesting.exampleCutoffMismatch_rejected
#print axioms RHFullWitnessedClosure.CoordinateTesting.exampleBadInequality_rejected
#print axioms RHFullWitnessedClosure.CoordinateTesting.exampleMissingSignAlternative_rejected

end RHFullWitnessedClosure.CoordinateTesting
