import HVRZetaComputationalProjection

/-! Independent conversion test; may fail without invalidating the value
definition or a separate propositional equality proof. -/
example : HVRZetaComputationalProjection.projectedZeta = riemannZeta := by
  rfl
