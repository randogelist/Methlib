import Std

/-! Frozen finite coordinate data; no analytic assumptions. -/

set_option autoImplicit false

namespace RHFullWitnessedClosure

abbrev FiniteCode := List Nat

structure ExactRat where
  numerator : Int
  denominator : Nat
deriving Repr, DecidableEq

structure CellCert where
  left : ExactRat
  right : ExactRat
  g2Lower : ExactRat
  g2Upper : ExactRat
  g3Lower : ExactRat
  g3Upper : ExactRat
  proofData : FiniteCode
deriving Repr, DecidableEq

structure NearCert where
  splitPoint : ExactRat
  proofData : FiniteCode
deriving Repr, DecidableEq

structure TailCert where
  cutoff : Nat
  proofData : FiniteCode
deriving Repr, DecidableEq

structure RawCert where
  spectralCutoff : Nat
  etaSplit : ExactRat
  nearCert : NearCert
  cells : List CellCert
  tailCert : TailCert
deriving Repr, DecidableEq

end RHFullWitnessedClosure
