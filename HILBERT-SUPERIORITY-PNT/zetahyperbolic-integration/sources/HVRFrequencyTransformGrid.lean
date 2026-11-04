import HVRFrequencyTransformCells
import HVRFrequencyGridWeights
import HVRPrimeLaplaceFrequencyBounds

/-!
Quantitative finite-cell error for the actual prime-density Laplace line.
The result controls a finite sum of cell-integral differences. The two cell
integrabilities remain explicit, as do positivity of R and a. It does not yet
rewrite the cell integrals into the full-frequency integral or identify the
sum with the coefficients in the weighted approximation adapter. No local
Lean run or theorem-level external audit has been performed on this file.
-/

noncomputable section
open Filter MeasureTheory
open HVRPrimeDensityFubiniBridge HVRPrimeDensityLaplace
open HVRFrequencyIntervalCells HVRFrequencyWeightedCoefficients
open scoped BigOperators

namespace HVRFrequencyTransformGrid

theorem finite_cells_lipschitz_error
    {ι : Type*} [DecidableEq ι] {μ : Measure ℝ}
    (S : Finset ι) (cell : ι → Set ℝ) (φ : ℝ → ℂ) (T : ℝ → ℂ)
    (sample : ι → ℝ) (δ M : ℝ) (hδ : 0 ≤ δ) (hM : 0 ≤ M)
    (hLip : ∀ t r : ℝ, ‖T t - T r‖ ≤ |t - r| * M)
    (hφ : Integrable φ μ)
    (hcell : ∀ i ∈ S, MeasurableSet (cell i))
    (hdisj : Set.Pairwise (↑S : Set ι) (fun i j => Disjoint (cell i) (cell j)))
    (hf : ∀ i ∈ S, IntegrableOn (fun t : ℝ => φ t * T t) (cell i) μ)
    (hg : ∀ i ∈ S, IntegrableOn (fun t : ℝ => φ t * T (sample i)) (cell i) μ)
    (hclose : ∀ i ∈ S, ∀ᵐ t : ℝ ∂μ.restrict (cell i), |t - sample i| ≤ δ) :
    ‖∑ i ∈ S,
      ((∫ t : ℝ in cell i, φ t * T t ∂μ) -
        (∫ t : ℝ in cell i, φ t * T (sample i) ∂μ))‖ ≤
      (δ * M) * ∫ t : ℝ, ‖φ t‖ ∂μ := by
  calc
    ‖∑ i ∈ S,
      ((∫ t : ℝ in cell i, φ t * T t ∂μ) -
        (∫ t : ℝ in cell i, φ t * T (sample i) ∂μ))‖ ≤
      ∑ i ∈ S, ‖(∫ t : ℝ in cell i, φ t * T t ∂μ) -
        (∫ t : ℝ in cell i, φ t * T (sample i) ∂μ)‖ := norm_sum_le S _
    _ ≤ ∑ i ∈ S, (δ * M) * ∫ t : ℝ in cell i, ‖φ t‖ ∂μ := by
      apply Finset.sum_le_sum
      intro i hi
      exact HVRFrequencyTransformCells.integral_cell_lipschitz_error
        (cell i) φ T (sample i) δ M hM hLip (hf i hi) (hg i hi)
        (hφ.norm.mono_measure Measure.restrict_le_self) (hclose i hi)
    _ = (δ * M) * ∑ i ∈ S, ∫ t : ℝ in cell i, ‖φ t‖ ∂μ := by
      rw [Finset.mul_sum]
    _ ≤ (δ * M) * ∫ t : ℝ, ‖φ t‖ ∂μ :=
      mul_le_mul_of_nonneg_left
        (HVRFrequencyCellBudget.disjoint_cells_integral_norm_sum_le S cell φ hφ hcell hdisj)
        (mul_nonneg hδ hM)

/-- Prime-density frequency-line grid error; cell mode integrability remains
explicit and no assertion is made about covering the test-function support. -/
theorem actual_prime_grid_cell_error
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
  have h := finite_cells_lipschitz_error (Finset.range N) (gridCell R N)
    (weightedFrequency ψ x)
    (fun t : ℝ => primeDensityLaplace ((a : ℂ) + (t : ℂ) * Complex.I))
    (gridPoint R N) (2 * R / (N : ℝ)) M hδ hM
    (fun t r => HVRPrimeLaplaceFrequencyBounds.primeDensityLaplace_frequency_lipschitz a t r ha)
    (weightedFrequency_integrable ψ x hψ)
    (fun i hi => gridCells_measurable R N i)
    (gridCells_pairwise_disjoint R N hR) hf hg (gridCells_close_ae R N)
  simpa only [M, norm_weightedFrequency] using h

end HVRFrequencyTransformGrid
