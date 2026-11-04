import HVRPrimeDirectGrid

/-!
Candidate discharge of the two actual frequency-cell integrability premises.
The proof uses a Lipschitz bound and a one-variable L1 majorant on each cell.
It does not claim the full quadrature limit, Fubini replacement, or PNT root.
No Lean execution or audit has yet been performed for this file.
-/

noncomputable section
open Filter MeasureTheory
open HVRPrimeDensityFubiniBridge HVRPrimeDensityLaplace
open HVRFrequencyIntervalCells HVRFrequencyWeightedCoefficients
open scoped BigOperators

namespace HVRPrimeGridIntegrability

theorem weighted_lipschitz_integrable_on_cell
    {μ : Measure ℝ} (cell : Set ℝ) (φ : ℝ → ℂ) (T : ℝ → ℂ)
    (sample δ M : ℝ) (hδ : 0 ≤ δ) (hM : 0 ≤ M)
    (hT : Continuous T)
    (hLip : ∀ t r : ℝ, ‖T t - T r‖ ≤ |t - r| * M)
    (hφ : Integrable φ μ)
    (hclose : ∀ᵐ t : ℝ ∂μ.restrict cell, |t - sample| ≤ δ) :
    IntegrableOn (fun t : ℝ => φ t * T t) cell μ := by
  let C : ℝ := ‖T sample‖ + δ * M
  have hφcell : IntegrableOn φ cell μ := hφ.mono_measure Measure.restrict_le_self
  have hmajor : IntegrableOn (fun t : ℝ => C * ‖φ t‖) cell μ :=
    hφcell.norm.const_mul C
  have hmeas : AEStronglyMeasurable (fun t : ℝ => φ t * T t) (μ.restrict cell) :=
    hφcell.aestronglyMeasurable.mul hT.measurable.aestronglyMeasurable
  apply Integrable.mono' hmajor hmeas
  filter_upwards [hclose] with t ht
  have htri : ‖T t‖ ≤ ‖T t - T sample‖ + ‖T sample‖ := by
    simpa only [sub_add_cancel] using norm_add_le (T t - T sample) (T sample)
  have hbound : ‖T t‖ ≤ C := by
    dsimp [C]
    have hdist := mul_le_mul_of_nonneg_right ht hM
    linarith [hLip t sample]
  calc
    ‖φ t * T t‖ = ‖φ t‖ * ‖T t‖ := norm_mul _ _
    _ ≤ ‖φ t‖ * C := mul_le_mul_of_nonneg_left hbound (norm_nonneg _)
    _ = C * ‖φ t‖ := mul_comm _ _

theorem primeDensity_frequency_continuous (a : ℝ) (ha : 0 < a) :
    Continuous (fun t : ℝ => primeDensityLaplace ((a : ℂ) + (t : ℂ) * Complex.I)) := by
  let M : ℝ := ∫ u : ℝ in Set.Ioi 0, |u| * ‖dampedError a u‖
  have hM : 0 ≤ M := by
    dsimp [M]
    exact integral_nonneg (fun u => mul_nonneg (abs_nonneg u) (norm_nonneg _))
  let K : NNReal := ⟨M, hM⟩
  have hL : LipschitzWith K
      (fun t : ℝ => primeDensityLaplace ((a : ℂ) + (t : ℂ) * Complex.I)) := by
    apply LipschitzWith.of_dist_le_mul
    intro t r
    simpa [dist_eq_norm, Real.norm_eq_abs, K, M, mul_comm] using
      HVRPrimeDirectFrequency.primeDensity_frequency_lipschitz_direct a t r ha
  exact hL.continuous

theorem actual_prime_grid_error_no_cell_integrability
    (R : ℝ) (N : ℕ) (ψ : ℝ → ℂ) (x a : ℝ)
    (hR : 0 ≤ R) (ha : 0 < a) (hψ : Integrable ψ) :
    ‖∑ i ∈ Finset.range N,
      ((∫ t : ℝ in gridCell R N i, weightedFrequency ψ x t *
        primeDensityLaplace ((a : ℂ) + (t : ℂ) * Complex.I)) -
       (∫ t : ℝ in gridCell R N i, weightedFrequency ψ x t *
        primeDensityLaplace ((a : ℂ) + (gridPoint R N i : ℂ) * Complex.I)))‖ ≤
      ((2 * R / (N : ℝ)) *
        (∫ u : ℝ in Set.Ioi 0, |u| * ‖dampedError a u‖)) *
        ∫ t : ℝ, ‖ψ t‖ := by
  let M : ℝ := ∫ u : ℝ in Set.Ioi 0, |u| * ‖dampedError a u‖
  let T : ℝ → ℂ := fun t => primeDensityLaplace ((a : ℂ) + (t : ℂ) * Complex.I)
  have hM : 0 ≤ M := by
    dsimp [M]
    exact integral_nonneg (fun u => mul_nonneg (abs_nonneg u) (norm_nonneg _))
  have hδ : 0 ≤ 2 * R / (N : ℝ) := by positivity
  have hφ := weightedFrequency_integrable ψ x hψ
  apply HVRPrimeDirectGrid.actual_prime_grid_cell_error_direct R N ψ x a hR ha hψ
  · intro i hi
    exact weighted_lipschitz_integrable_on_cell (gridCell R N i)
      (weightedFrequency ψ x) T (gridPoint R N i) (2 * R / (N : ℝ)) M hδ hM
      (primeDensity_frequency_continuous a ha)
      (fun t r => HVRPrimeDirectFrequency.primeDensity_frequency_lipschitz_direct a t r ha)
      hφ (gridCells_close_ae R N i hi)
  · intro i hi
    exact (hφ.mono_measure Measure.restrict_le_self).mul_const _

end HVRPrimeGridIntegrability
