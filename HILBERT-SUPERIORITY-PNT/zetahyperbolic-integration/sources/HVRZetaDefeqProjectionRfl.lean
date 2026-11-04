import HVRZetaDefeqProjectionEquality

/-! Separate named and audited definitional equality check. Its type mentions
`riemannZeta`; it does not establish root swap independence. -/
noncomputable section
namespace HVRZetaDefeqProjection
theorem rawZeta_defeq_riemannZeta : rawZeta = riemannZeta := by
  rfl
end HVRZetaDefeqProjection
