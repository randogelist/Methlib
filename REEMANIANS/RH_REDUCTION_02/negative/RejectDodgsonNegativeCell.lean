import RHFinitePruning.DodgsonCells

-- A certified negative Turan numerator cannot pass the strict test.
example : RHFinitePruning.Dodgson.negativeControl.necessaryTest = true := by
  rw [RHFinitePruning.Dodgson.negativeControl_rejected]
  decide
