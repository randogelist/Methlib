import HVRZetaDefeqProjection

/-! Three trivial equalities to inspect how a `change` to a definitionally
equal function affects declaration-level dependency traversal. These do not
establish any analytic fact, no-swap PNT result, or semantic independence. -/
noncomputable section
namespace HVRZetaChangeExperiment
open HVRZetaDefeqProjection

theorem raw_reflexivity (s : ℂ) : rawZeta s = rawZeta s := by
  rfl

theorem raw_statement_changed_to_zeta (s : ℂ) : rawZeta s = rawZeta s := by
  change riemannZeta s = riemannZeta s
  rfl

theorem zeta_statement_changed_to_raw (s : ℂ) : riemannZeta s = riemannZeta s := by
  change rawZeta s = rawZeta s
  rfl

end HVRZetaChangeExperiment
