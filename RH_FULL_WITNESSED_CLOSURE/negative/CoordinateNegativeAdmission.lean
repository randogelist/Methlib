import CoordinateTesting

open RHFullWitnessedClosure.CoordinateTesting

-- EXPECTED_RESULT=KERNEL_DECISION_REJECTION
example : coordinateCheck exampleBadDenominator = true := by
  decide
