import HVRPrimeDirectFrequency

/-! Actual finite grid cell error with the direct one-variable prime-frequency
Lipschitz proof. Mode-integrability premises remain explicit. Uncompiled until
matching external CI and theorem-level audit. -/

noncomputable section
open Filter MeasureTheory
open HVRPrimeDensityFubiniBridge HVRPrimeDensityLaplace
open HVRFrequencyIntervalCells HVRFrequencyWeightedCoefficients
open scoped BigOperators

namespace HVRPrimeDirectGrid

theorem actual_prime_grid_cell_error_direct
    (R : ℝ) (N : ℕ) (ψ : ℝ → ℂ) (x a : ℝ)
    (hR : 0 ≤ R) (ha : 0 < a) (hψ : Integrable ψ)
    (hf : ∀ i ∈ Finset.range N, IntegrableOn
      (fun t : ℝ => weightedFrequency ψ x t *
        primeDensityLaplace ((a : ℂ) + (t : ℂ) * Complex.I)) (gridCell R N i))
    (hg : ∀ i ∈ Finset.range N, IntegrableOn
      (fun t : ℝ => weightedFrequency ψ x t *
        primeDensityLaplace ((a : ℂ) + (gridPoint R N i : ℂ) * Complex.I)) (gridCell R N i)) :
    ‖∑ i ∈ Finset.range N,
      ((∫ t : ℝ in gridCell R N i, weightedFrequency ψ x t *
        primeDensityLaplace ((a : ℂ) + (t : ℂ) * Complex.I)) -
       (∫ t : ℝ in gridCell R N i, weightedFrequency ψ x t *
        primeDensityLaplace ((a : ℂ) + (gridPoint R N i : ℂ) * Complex.I)))‖ ≤
      ((2 * R / (N : ℝ)) *
        (∫ u : ℝ in Set.Ioi 0, |u| * ‖dampedError a u‖)) *
        ∫ t : ℝ, ‖ψ t‖ := by
  let M : ℝ := ∫ u : ℝ in Set.Ioi 0, |u| * ‖dampedError a u‖
  have hM : 0 ≤ M := by
    dsimp [M]
    exact integral_nonneg (fun u => mul_nonneg (abs_nonneg u) (norm_nonneg _))
  have hδ : 0 ≤ 2 * R / (N : ℝ) := by positivity
  have h := HVRFrequencyTransformGrid.finite_cells_lipschitz_error (Finset.range N) (gridCell R N)
    (weightedFrequency ψ x)
    (fun t : ℝ => primeDensityLaplace ((a : ℂ) + (t : ℂ) * Complex.I))
    (gridPoint R N) (2 * R / (N : ℝ)) M hδ hM
    (fun t r => HVRPrimeDirectFrequency.primeDensity_frequency_lipschitz_direct a t r ha)
    (weightedFrequency_integrable ψ x hψ)
    (fun i hi => gridCells_measurable R N i)
    (gridCells_pairwise_disjoint R N hR) hf hg (gridCells_close_ae R N)
  simpa only [M, norm_weightedFrequency] using h


end HVRPrimeDirectGrid
