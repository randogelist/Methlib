import HVRZetaComputationalProjection

/-! Candidate only. This equality's statement mentions Mathlib's zeta, so a
declaration graph traversing types will necessarily visit the old zeta. -/
noncomputable section
namespace HVRZetaComputationalProjection

theorem projectedZeta_eq_riemannZeta : projectedZeta = riemannZeta := by
  classical
  simp [projectedZeta, projectedLambda, modifiedTheta,
    riemannZeta, HurwitzZeta.hurwitzZetaEven,
    HurwitzZeta.completedHurwitzZetaEven, WeakFEPair.Λ,
    WeakFEPair.Λ₀, WeakFEPair.f_modif, HurwitzZeta.hurwitzEvenFEPair]

end HVRZetaComputationalProjection
