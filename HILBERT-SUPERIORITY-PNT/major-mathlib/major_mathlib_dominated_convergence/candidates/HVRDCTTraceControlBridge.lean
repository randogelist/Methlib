import HVRDCTTraceControlLeaf

/-! Positive control through a separately compiled declaration. -/
noncomputable section
open Filter MeasureTheory
open scoped Topology

namespace HVRDCTTraceControlBridge

theorem indirect_target (F : ℕ → ℝ → ℂ) (f : ℝ → ℂ) (bound : ℝ → ℝ)
    (hmeas : ∀ n, AEStronglyMeasurable (F n) volume)
    (hbound_integrable : Integrable bound volume)
    (hbound : ∀ n, ∀ᵐ t : ℝ ∂volume, ‖F n t‖ ≤ bound t)
    (hlim : ∀ᵐ t : ℝ ∂volume, Tendsto (fun n : ℕ => F n t) atTop (𝓝 (f t))) :
    Tendsto (fun n : ℕ => ∫ t : ℝ, F n t) atTop (𝓝 (∫ t : ℝ, f t)) :=
  HVRDCTTraceControlLeaf.direct_target F f bound hmeas hbound_integrable hbound hlim


/-- Countably generated filter endpoint behind a second module. -/
theorem indirect_filter_target (F : ℕ → ℝ → ℂ) (f : ℝ → ℂ) (bound : ℝ → ℝ)
    (hmeas : ∀ᶠ n : ℕ in atTop, AEStronglyMeasurable (F n) volume)
    (hbound : ∀ᶠ n : ℕ in atTop, ∀ᵐ t : ℝ ∂volume, ‖F n t‖ ≤ bound t)
    (hbound_integrable : Integrable bound volume)
    (hlim : ∀ᵐ t : ℝ ∂volume, Tendsto (fun n : ℕ => F n t) atTop (𝓝 (f t))) :
    Tendsto (fun n : ℕ => ∫ t : ℝ, F n t) atTop (𝓝 (∫ t : ℝ, f t)) :=
  HVRDCTTraceControlLeaf.direct_filter_target F f bound hmeas hbound hbound_integrable hlim

end HVRDCTTraceControlBridge
