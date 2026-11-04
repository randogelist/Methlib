import HVRZetaHyperbolicFrequencyBounds
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
Candidate one-cell approximation bound for a Fourier frequency integral.

The mode integrabilities and an almost-everywhere bound on cell width are
explicit. Constructing a finite partition, proving those integrabilities for
the actual frequency test, and summing cell errors are separate obligations.
No local Lean run or matching external audit has been performed.
-/

noncomputable section
open Filter MeasureTheory
open HVRZetaHyperbolicFrequencyBounds

namespace HVRFrequencyCellError

/-- A frequency cell can be replaced by one sample with a weighted error. -/
theorem integral_cell_phase_error
    {μ : Measure ℝ} (cell : Set ℝ) (φ : ℝ → ℂ) (sample u δ : ℝ)
    (hf : IntegrableOn (fun t : ℝ => φ t * phase t u) cell μ)
    (hg : IntegrableOn (fun t : ℝ => φ t * phase sample u) cell μ)
    (hφ : IntegrableOn (fun t : ℝ => ‖φ t‖) cell μ)
    (hclose : ∀ᵐ t : ℝ ∂μ.restrict cell, |t - sample| ≤ δ) :
    ‖(∫ t : ℝ in cell, φ t * phase t u ∂μ) -
      (∫ t : ℝ in cell, φ t * phase sample u ∂μ)‖ ≤
        (δ * |u|) * ∫ t : ℝ in cell, ‖φ t‖ ∂μ := by
  have hw : IntegrableOn (fun t : ℝ => |u| * ‖φ t‖) cell μ :=
    hφ.const_mul |u|
  have hbound : ∀ᵐ t : ℝ ∂μ.restrict cell,
      ‖φ t * phase t u - φ t * phase sample u‖ ≤
        δ * (|u| * ‖φ t‖) := by
    filter_upwards [hclose] with t ht
    calc
      ‖φ t * phase t u - φ t * phase sample u‖ =
          ‖φ t‖ * ‖phase t u - phase sample u‖ := by
        rw [← mul_sub, norm_mul]
      _ ≤ ‖φ t‖ * (|t - sample| * |u|) :=
        mul_le_mul_of_nonneg_left (phase_frequency_lipschitz t sample u) (norm_nonneg _)
      _ ≤ ‖φ t‖ * (δ * |u|) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ht (abs_nonneg u))
          (norm_nonneg _)
      _ = δ * (|u| * ‖φ t‖) := by ring
  have h := HVRNativeDominatedLimit.integral_error_le_weighted
    (μ := μ.restrict cell) δ hf hg hw hbound
  simpa only [integral_const_mul, mul_assoc] using h

end HVRFrequencyCellError

