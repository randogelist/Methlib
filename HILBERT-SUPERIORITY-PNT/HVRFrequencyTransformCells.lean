import HVRFrequencyCellBudget

/-!
One-dimensional cell bound for a Lipschitz frequency transform. It applies
to the actual prime-density Laplace line once its known Lipschitz constant
and the explicit integrability premises are supplied. This does not prove a
partition covers the test support, a full quadrature error, or either PNT
limit. Uncompiled candidate; no external audit has been performed.
-/

noncomputable section
open Filter MeasureTheory

namespace HVRFrequencyTransformCells

theorem integral_cell_lipschitz_error
    {μ : Measure ℝ} (cell : Set ℝ) (φ : ℝ → ℂ) (T : ℝ → ℂ)
    (sample δ M : ℝ) (hM : 0 ≤ M)
    (hLip : ∀ t r : ℝ, ‖T t - T r‖ ≤ |t - r| * M)
    (hf : IntegrableOn (fun t : ℝ => φ t * T t) cell μ)
    (hg : IntegrableOn (fun t : ℝ => φ t * T sample) cell μ)
    (hφ : IntegrableOn (fun t : ℝ => ‖φ t‖) cell μ)
    (hclose : ∀ᵐ t : ℝ ∂μ.restrict cell, |t - sample| ≤ δ) :
    ‖(∫ t : ℝ in cell, φ t * T t ∂μ) -
      (∫ t : ℝ in cell, φ t * T sample ∂μ)‖ ≤
        (δ * M) * ∫ t : ℝ in cell, ‖φ t‖ ∂μ := by
  have hw : IntegrableOn (fun t : ℝ => M * ‖φ t‖) cell μ := hφ.const_mul M
  have hbound : ∀ᵐ t : ℝ ∂μ.restrict cell,
      ‖φ t * T t - φ t * T sample‖ ≤ δ * (M * ‖φ t‖) := by
    filter_upwards [hclose] with t ht
    calc
      ‖φ t * T t - φ t * T sample‖ = ‖φ t‖ * ‖T t - T sample‖ := by
        rw [← mul_sub, norm_mul]
      _ ≤ ‖φ t‖ * (|t - sample| * M) :=
        mul_le_mul_of_nonneg_left (hLip t sample) (norm_nonneg _)
      _ ≤ ‖φ t‖ * (δ * M) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ht hM) (norm_nonneg _)
      _ = δ * (M * ‖φ t‖) := by ring
  have h := HVRNativeDominatedLimit.integral_error_le_weighted
    (μ := μ.restrict cell) δ hf hg hw hbound
  simpa only [integral_const_mul, mul_assoc] using h

end HVRFrequencyTransformCells
