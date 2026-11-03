import HVR_SpectralSeedCorrelation

noncomputable section
open HVRSpectralSeedCorrelation

/-! Candidate compact-support packaging for the previously audited support
bound. No Fourier identification, continuity, or PNT is claimed here.
No local Lean was executed. -/
namespace HVRSpectralCorrelationCompact

theorem correlation_hasCompactSupport (w : ℝ) (hw : 0 < w) :
    HasCompactSupport (correlation w hw) := by
  apply HasCompactSupport.intro (K := Set.Icc (-w) w) isCompact_Icc
  intro t ht
  apply correlation_zero_of_band w hw t
  by_contra hn
  have habs : |t| < w := lt_of_not_ge hn
  have ht' : t ∈ Set.Icc (-w) w := by
    exact ⟨le_of_lt (abs_lt.mp habs).1, le_of_lt (abs_lt.mp habs).2⟩
  exact ht ht'

def complexCorrelation (w : ℝ) (hw : 0 < w) : ℝ → ℂ :=
  Complex.ofReal ∘ correlation w hw

theorem complexCorrelation_hasCompactSupport (w : ℝ) (hw : 0 < w) :
    HasCompactSupport (complexCorrelation w hw) := by
  exact (correlation_hasCompactSupport w hw).comp_left (show Complex.ofReal 0 = 0 by simp)

end HVRSpectralCorrelationCompact
