import HVRZetaDefeqProjection

/-! This exploratory theorem mentions `riemannZeta` in its statement, so its
declaration graph is expected to include that constant and its dependencies.
It is not a no-swap proof of the PNT. -/
noncomputable section
namespace HVRZetaDefeqProjection

theorem rawZeta_eq_riemannZeta : rawZeta = riemannZeta := by
  classical
  simp [rawZeta, rawLambda, rawModifiedTheta, zeroConstant,
    riemannZeta, HurwitzZeta.hurwitzZetaEven,
    HurwitzZeta.completedHurwitzZetaEven, WeakFEPair.Λ,
    WeakFEPair.Λ₀, WeakFEPair.f_modif, HurwitzZeta.hurwitzEvenFEPair]

#print axioms HVRZetaDefeqProjection.rawZeta_eq_riemannZeta

end HVRZetaDefeqProjection
