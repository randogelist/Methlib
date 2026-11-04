import HVRFrequencyCellError

/-!
Candidate finite aggregation of the audited one-cell phase-error estimate.
No disjointness or coverage claim is made. The scalar budget for the sum of
cell integrals is an explicit hypothesis; deriving it for an actual partition
and taking a mesh-to-zero limit remain separate obligations.
-/

noncomputable section
open Filter MeasureTheory
open HVRZetaHyperbolicFrequencyBounds HVRFrequencyCellError

namespace HVRFrequencyFiniteCells

/-- Finite frequency-cell errors are controlled by a common mesh and budget. -/
theorem finite_cells_phase_error
    {ι : Type*} [DecidableEq ι] {μ : Measure ℝ}
    (S : Finset ι) (cell : ι → Set ℝ) (φ : ℝ → ℂ)
    (sample : ι → ℝ) (u δ budget : ℝ) (hδ : 0 ≤ δ)
    (hf : ∀ i ∈ S, IntegrableOn (fun t : ℝ => φ t * phase t u) (cell i) μ)
    (hg : ∀ i ∈ S, IntegrableOn (fun t : ℝ => φ t * phase (sample i) u) (cell i) μ)
    (hφ : ∀ i ∈ S, IntegrableOn (fun t : ℝ => ‖φ t‖) (cell i) μ)
    (hclose : ∀ i ∈ S, ∀ᵐ t : ℝ ∂μ.restrict (cell i), |t - sample i| ≤ δ)
    (hbudget : (∑ i ∈ S, ∫ t : ℝ in cell i, ‖φ t‖ ∂μ) ≤ budget) :
    ‖∑ i ∈ S,
        ((∫ t : ℝ in cell i, φ t * phase t u ∂μ) -
          (∫ t : ℝ in cell i, φ t * phase (sample i) u ∂μ))‖ ≤
      (δ * |u|) * budget := by
  calc
    ‖∑ i ∈ S,
        ((∫ t : ℝ in cell i, φ t * phase t u ∂μ) -
          (∫ t : ℝ in cell i, φ t * phase (sample i) u ∂μ))‖ ≤
        ∑ i ∈ S, ‖(∫ t : ℝ in cell i, φ t * phase t u ∂μ) -
          (∫ t : ℝ in cell i, φ t * phase (sample i) u ∂μ)‖ :=
      norm_sum_le S _
    _ ≤ ∑ i ∈ S, (δ * |u|) * ∫ t : ℝ in cell i, ‖φ t‖ ∂μ := by
      apply Finset.sum_le_sum
      intro i hi
      exact integral_cell_phase_error (cell i) φ (sample i) u δ
        (hf i hi) (hg i hi) (hφ i hi) (hclose i hi)
    _ = (δ * |u|) * ∑ i ∈ S, ∫ t : ℝ in cell i, ‖φ t‖ ∂μ := by
      rw [Finset.mul_sum]
    _ ≤ (δ * |u|) * budget :=
      mul_le_mul_of_nonneg_left hbudget (mul_nonneg hδ (abs_nonneg u))

end HVRFrequencyFiniteCells

