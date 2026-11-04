import HVRFrequencyFiniteCells
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
Finite-frequency quadrature mass budget for an arbitrary integrable weight.

This discharges the `hbudget` input in `finite_cells_phase_error` whenever
the finite frequency cells are measurable and pairwise disjoint.  It also
establishes a uniform budget for the actual complex quadrature coefficients.
No assumption of compactness, partition coverage, sample placement, or an
interchange of two continuous integrals is needed for these statements.

This is an uncompiled candidate. An external cached Lean 4.34.0-rc1 build,
theorem-level axiom audit, and transitive target dependency trace are required.
-/

noncomputable section
open Filter MeasureTheory
open scoped BigOperators

namespace HVRFrequencyCellBudget

/-- Pairwise disjoint measurable cells cannot have more L1 mass than the
underlying measure.  This is a one-variable estimate. -/
theorem disjoint_cells_integral_norm_sum_le
    {ι : Type*} [DecidableEq ι] {μ : Measure ℝ}
    (S : Finset ι) (cell : ι → Set ℝ) (φ : ℝ → ℂ)
    (hφ : Integrable φ μ)
    (hcell : ∀ i ∈ S, MeasurableSet (cell i))
    (hdisj : Set.Pairwise (↑S : Set ι) (Disjoint on cell)) :
    (∑ i ∈ S, ∫ t : ℝ in cell i, ‖φ t‖ ∂μ) ≤
      ∫ t : ℝ, ‖φ t‖ ∂μ := by
  have hint : ∀ i ∈ S, IntegrableOn (fun t : ℝ => ‖φ t‖) (cell i) μ := by
    intro i hi
    exact hφ.norm.mono_measure Measure.restrict_le_self
  have hunion := integral_biUnion_finset (μ := μ) (f := fun t : ℝ => ‖φ t‖)
    S hcell hdisj hint
  rw [← hunion]
  exact integral_mono_measure Measure.restrict_le_self
    (Filter.Eventually.of_forall (fun t => norm_nonneg (φ t))) hφ.norm

/-- The absolute sum of the cell-integral coefficients has the same L1
budget.  Integrating a weight before sampling requires no continuity of it. -/
theorem disjoint_cells_coefficient_norm_sum_le
    {ι : Type*} [DecidableEq ι] {μ : Measure ℝ}
    (S : Finset ι) (cell : ι → Set ℝ) (φ : ℝ → ℂ)
    (hφ : Integrable φ μ)
    (hcell : ∀ i ∈ S, MeasurableSet (cell i))
    (hdisj : Set.Pairwise (↑S : Set ι) (Disjoint on cell)) :
    (∑ i ∈ S, ‖∫ t : ℝ in cell i, φ t ∂μ‖) ≤
      ∫ t : ℝ, ‖φ t‖ ∂μ := by
  calc
    (∑ i ∈ S, ‖∫ t : ℝ in cell i, φ t ∂μ‖) ≤
        ∑ i ∈ S, ∫ t : ℝ in cell i, ‖φ t‖ ∂μ := by
          apply Finset.sum_le_sum
          intro i hi
          exact norm_integral_le_integral_norm (μ := μ.restrict (cell i)) φ
    _ ≤ ∫ t : ℝ, ‖φ t‖ ∂μ :=
      disjoint_cells_integral_norm_sum_le S cell φ hφ hcell hdisj

/-- The finite-cell phase estimate with its mass-budget premise discharged. -/
theorem finite_cells_phase_error_of_disjoint
    {ι : Type*} [DecidableEq ι] {μ : Measure ℝ}
    (S : Finset ι) (cell : ι → Set ℝ) (φ : ℝ → ℂ)
    (sample : ι → ℝ) (u δ : ℝ) (hδ : 0 ≤ δ)
    (hφ : Integrable φ μ)
    (hcell : ∀ i ∈ S, MeasurableSet (cell i))
    (hdisj : Set.Pairwise (↑S : Set ι) (Disjoint on cell))
    (hf : ∀ i ∈ S, IntegrableOn
      (fun t : ℝ => φ t * HVRZetaHyperbolicFrequencyBounds.phase t u) (cell i) μ)
    (hg : ∀ i ∈ S, IntegrableOn
      (fun t : ℝ => φ t * HVRZetaHyperbolicFrequencyBounds.phase (sample i) u) (cell i) μ)
    (hclose : ∀ i ∈ S, ∀ᵐ t : ℝ ∂μ.restrict (cell i), |t - sample i| ≤ δ) :
    ‖∑ i ∈ S,
        ((∫ t : ℝ in cell i, φ t * HVRZetaHyperbolicFrequencyBounds.phase t u ∂μ) -
          (∫ t : ℝ in cell i, φ t * HVRZetaHyperbolicFrequencyBounds.phase (sample i) u ∂μ))‖ ≤
      (δ * |u|) * ∫ t : ℝ, ‖φ t‖ ∂μ := by
  apply HVRFrequencyFiniteCells.finite_cells_phase_error S cell φ sample u δ
    (∫ t : ℝ, ‖φ t‖ ∂μ) hδ hf hg
  · intro i hi
    exact hφ.norm.mono_measure Measure.restrict_le_self
  · exact hclose
  · exact disjoint_cells_integral_norm_sum_le S cell φ hφ hcell hdisj

end HVRFrequencyCellBudget
