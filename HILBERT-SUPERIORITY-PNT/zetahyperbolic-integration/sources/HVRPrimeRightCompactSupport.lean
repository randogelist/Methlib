import HVRPrimeRightQuadrature
import Mathlib.Analysis.Normed.Group.Bounded

/-! Candidate for choosing the finite grid interval from compact support.
No local Lean execution or external audit has been performed. -/

noncomputable section
open Filter MeasureTheory
open HVRPrimeDensityFubiniBridge HVRPrimeDensityLaplace
open HVRFrequencyWeightedCoefficients
open scoped Topology

namespace HVRPrimeRightCompactSupport

/-- Every compactly supported frequency test is zero outside one grid interval. -/
theorem exists_grid_support_radius (ψ : ℝ → ℂ) (hcompact : HasCompactSupport ψ) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ᵐ t : ℝ, t ∉ Set.Ioc (-R) R → ψ t = 0 := by
  obtain ⟨R, hR, hzero⟩ := hcompact.exists_pos_le_norm
  refine ⟨R, le_of_lt hR, ?_⟩
  filter_upwards [] with t ht
  apply hzero t
  rw [Real.norm_eq_abs]
  have ht' : ¬ (-R < t ∧ t ≤ R) := ht
  push_neg at ht'
  rcases ht' with hleft | hright
  · have hneg : t ≤ 0 := by linarith
    rw [abs_of_nonpos hneg]
    linarith
  · have hpos : 0 ≤ t := by linarith
    rw [abs_of_nonneg hpos]
    linarith

/-- The right-hand full-line approximation for an integrable compactly
supported frequency test, with a chosen finite grid radius. -/
theorem exists_compact_right_grid_limit (ψ : ℝ → ℂ) (x a : ℝ)
    (ha : 0 < a) (hψ : Integrable ψ) (hcompact : HasCompactSupport ψ) :
    ∃ R : ℝ, 0 ≤ R ∧ Tendsto
      (fun N : ℕ => HVRPrimeRightQuadrature.sampledRightGrid R N ψ x a) atTop
      (𝓝 (∫ t : ℝ, weightedFrequency ψ x t *
        primeDensityLaplace ((a : ℂ) + (t : ℂ) * Complex.I))) := by
  obtain ⟨R, hR, hsupport⟩ := exists_grid_support_radius ψ hcompact
  exact ⟨R, hR, HVRPrimeRightQuadrature.sampledRightGrid_tendsto_full
    R ψ x a hR ha hψ hsupport⟩

end HVRPrimeRightCompactSupport
