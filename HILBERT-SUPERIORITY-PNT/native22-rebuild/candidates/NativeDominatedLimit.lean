import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-!
A quantitative weighted-uniform convergence route for selected integral
limits.  This is not the general dominated convergence theorem: it requires
integrability of every integrand, an integrable real weight, and a scalar
error bound tending to zero whose product with the weight dominates each
pointwise error almost everywhere.  A compact-support application must prove
these hypotheses separately.

The proof uses basic Bochner integral norm and linearity inequalities, not
an explicit call to the dominated-convergence endpoints. This source is
uncompiled and unaudited. Recursive theorem dependencies of those basic
inequalities still need inspection before any independence claim.
-/

noncomputable section

open Filter MeasureTheory
open scoped Topology

namespace HVRNativeDominatedLimit

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- Weighted pointwise error gives an explicit integral error bound. -/
theorem integral_error_le_weighted
    {f g : α → ℂ} {weight : α → ℝ} (e : ℝ)
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hw : Integrable weight μ)
    (hbound : ∀ᵐ x ∂μ, ‖f x - g x‖ ≤ e * weight x) :
    ‖(∫ x, f x ∂μ) - (∫ x, g x ∂μ)‖ ≤ e * ∫ x, weight x ∂μ := by
  rw [← integral_sub hf hg]
  calc
    ‖∫ x, (f x - g x) ∂μ‖ ≤ ∫ x, e * weight x ∂μ :=
      norm_integral_le_of_norm_le (hw.const_mul e) hbound
    _ = e * ∫ x, weight x ∂μ := integral_const_mul e weight

/-- Integral convergence under the stronger weighted-uniform error condition. -/
theorem integral_tendsto_of_weighted_uniform_error
    {f : ℕ → α → ℂ} {g : α → ℂ} {weight : α → ℝ} {e : ℕ → ℝ}
    (hf : ∀ n, Integrable (f n) μ) (hg : Integrable g μ)
    (hw : Integrable weight μ) (he : Tendsto e atTop (𝓝 0))
    (hbound : ∀ n, ∀ᵐ x ∂μ, ‖f n x - g x‖ ≤ e n * weight x) :
    Tendsto (fun n => ∫ x, f n x ∂μ) atTop (𝓝 (∫ x, g x ∂μ)) := by
  have hprod : Tendsto (fun n => e n * ∫ x, weight x ∂μ) atTop (𝓝 0) := by
    have h := he.mul (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => ∫ x, weight x ∂μ) atTop (𝓝 (∫ x, weight x ∂μ)))
    simpa only [zero_mul] using h
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hprod
  exact integral_error_le_weighted (e n) (hf n) hg hw (hbound n)

end HVRNativeDominatedLimit
