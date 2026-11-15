import SingularClosure.NoetherClosure.EnstrophyBound

/-! NC03: use the *actual* Methlib finite physical six-channel Parseval identity. -/
set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory
open scoped ENNReal NNReal

namespace SingularClosure
noncomputable section

theorem NOETHER_SIX_CHANNEL_MATCH
    {ν : ℝ} {a : Field} {N : ℕ}
    (g : GalerkinSolution ν a N) (t : ℝ) :
    sixEnstrophy N (g.coeff t) = physicalEnstrophy (g.velocity t) := by
  simpa only [GalerkinSolution.velocity] using
    SIX_CHANNEL_FINITE_ENSTROPHY_EQ N (g.coeff t)

theorem NOETHER_UNIFORM_SIX_ENSTROPHY
    (hNoether : NOETHER_CHARGE_ADMISSION)
    (ν : ℝ) (hν : 0 < ν) (a : Field) (ha : SmoothSigmaZero a)
    (T : ℝ) (hT : 0 < T) :
    ∃ M : ℝ≥0,
      ∀ (N : ℕ), 1 ≤ N → ∀ (g : GalerkinSolution ν a N),
        ∀ t ∈ Icc (0 : ℝ) T,
          sixEnstrophy N (g.coeff t) ≤ (M : ℝ≥0∞) := by
  obtain ⟨M, hbound⟩ :=
    NOETHER_UNIFORM_PHYSICAL_ENSTROPHY hNoether ν hν a ha T hT
  refine ⟨M, ?_⟩
  intro N hN g t ht
  rw [NOETHER_SIX_CHANNEL_MATCH g t]
  exact hbound N hN g t ht

end
end SingularClosure
