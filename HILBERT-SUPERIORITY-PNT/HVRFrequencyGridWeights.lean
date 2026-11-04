import HVRFrequencyWeightedCoefficients
import HVRFrequencyIntervalCells

/-!
Combines the regular finite grid with the actual oscillatory frequency
coefficients. This establishes their uniform L1 budget only. It is a candidate:
no Lean compilation or theorem-level axiom audit has been run for this file.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace HVRFrequencyGridWeights

theorem actual_grid_coefficients_norm_sum_le
    {μ : Measure ℝ} (R : ℝ) (N : ℕ) (hR : 0 ≤ R)
    (ψ : ℝ → ℂ) (x : ℝ) (hψ : Integrable ψ μ) :
    (∑ i ∈ Finset.range N,
      ‖∫ t : ℝ in HVRFrequencyIntervalCells.gridCell R N i,
        HVRFrequencyWeightedCoefficients.weightedFrequency ψ x t ∂μ‖) ≤
      ∫ t : ℝ, ‖ψ t‖ ∂μ := by
  apply HVRFrequencyWeightedCoefficients.actual_coefficients_norm_sum_le
    (Finset.range N) (HVRFrequencyIntervalCells.gridCell R N) ψ x hψ
  · intro i hi
    exact HVRFrequencyIntervalCells.gridCells_measurable R N i
  · exact HVRFrequencyIntervalCells.gridCells_pairwise_disjoint R N hR

end HVRFrequencyGridWeights
