import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Positive control only. This declaration intentionally invokes the old
endpoint. It is not imported by the HVR candidate proof. -/
noncomputable section
open Filter MeasureTheory
open scoped Topology

namespace HVRDCTTraceControlLeaf

theorem direct_target (F : ℕ → ℝ → ℂ) (f : ℝ → ℂ) (bound : ℝ → ℝ)
    (hmeas : ∀ n, AEStronglyMeasurable (F n) volume)
    (hbound_integrable : Integrable bound volume)
    (hbound : ∀ n, ∀ᵐ t : ℝ ∂volume, ‖F n t‖ ≤ bound t)
    (hlim : ∀ᵐ t : ℝ ∂volume, Tendsto (fun n : ℕ => F n t) atTop (𝓝 (f t))) :
    Tendsto (fun n : ℕ => ∫ t : ℝ, F n t) atTop (𝓝 (∫ t : ℝ, f t)) :=
  MeasureTheory.tendsto_integral_of_dominated_convergence bound hmeas hbound_integrable hbound hlim


/-- A second positive control for the countably generated filter endpoint. -/
theorem direct_filter_target (F : ℕ → ℝ → ℂ) (f : ℝ → ℂ) (bound : ℝ → ℝ)
    (hmeas : ∀ᶠ n : ℕ in atTop, AEStronglyMeasurable (F n) volume)
    (hbound : ∀ᶠ n : ℕ in atTop, ∀ᵐ t : ℝ ∂volume, ‖F n t‖ ≤ bound t)
    (hbound_integrable : Integrable bound volume)
    (hlim : ∀ᵐ t : ℝ ∂volume, Tendsto (fun n : ℕ => F n t) atTop (𝓝 (f t))) :
    Tendsto (fun n : ℕ => ∫ t : ℝ, F n t) atTop (𝓝 (∫ t : ℝ, f t)) :=
  MeasureTheory.tendsto_integral_filter_of_dominated_convergence bound hmeas hbound
    hbound_integrable hlim

end HVRDCTTraceControlLeaf
