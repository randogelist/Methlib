import CoordinateTesting

set_option autoImplicit false

open RHFullWitnessedClosure
open RHFullWitnessedClosure.CoordinateTesting

example (w : RawCert) :
    coordinateCheck w = true ↔ CoordinateWellFormed w :=
  coordinateCheck_iff w

example (w : RawCert) (h : coordinateCheck w = true) :
    CoordinateWellFormed w := coordinateCheck_sound w h

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
