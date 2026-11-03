import HVRFallbackFourier
import HVROrdinaryFourier

/-!
Application of the compiled fallback compact-support Fourier theorem.
HVRFallbackFourier is adapted from Mathlib's RiemannLebesgueLemma.lean,
Copyright (c) 2022 David Loeffler, Apache License 2.0. This application does
not claim an independently discovered argument or transitive independence
from any Mathlib theorem. The negative Fourier-frequency direction is used
for the project's ordinary positive-frequency convention.
-/
noncomputable section
open Filter MeasureTheory NativeFourierDecay
open scoped Topology

namespace HVRFallbackApplications

theorem fourier_tendsto_atTop (g : ℝ → ℂ) (hg : Continuous g)
    (hcompact : HasCompactSupport g) :
    Tendsto (integralTransform g) atTop (𝓝 0) := by
  exact (HVRFallbackFourier.real_fourier_compact_decay g hg hcompact).mono_left
    atTop_le_cocompact

theorem fourier_tendsto_atBot (g : ℝ → ℂ) (hg : Continuous g)
    (hcompact : HasCompactSupport g) :
    Tendsto (integralTransform g) atBot (𝓝 0) := by
  exact (HVRFallbackFourier.real_fourier_compact_decay g hg hcompact).mono_left
    atBot_le_cocompact

theorem ordinary_tendsto_atTop (g : ℝ → ℂ) (hg : Continuous g)
    (hcompact : HasCompactSupport g) :
    Tendsto (HVROrdinaryFourier.ordinaryIntegral g) atTop (𝓝 0) :=
  HVROrdinaryFourier.ordinaryIntegral_tendsto_zero_of_atBot g
    (fourier_tendsto_atBot g hg hcompact)

/-- Weighted-boundary specialization; b is any continuous boundary function. -/
theorem weighted_boundary_tendsto_atTop (ψ b : ℝ → ℂ)
    (hψ : Continuous ψ) (hcompact : HasCompactSupport ψ) (hb : Continuous b) :
    Tendsto (fun x : ℝ => ∫ t : ℝ,
      (ψ t * Complex.exp ((t : ℂ) * Complex.I * (x : ℂ))) * b t)
      atTop (𝓝 0) := by
  have hg : Continuous (fun t : ℝ => ψ t * b t) := hψ.mul hb
  have hs : HasCompactSupport (fun t : ℝ => ψ t * b t) := hcompact.mul_right
  have h := ordinary_tendsto_atTop (fun t : ℝ => ψ t * b t) hg hs
  apply h.congr'
  filter_upwards [] with x
  unfold HVROrdinaryFourier.ordinaryIntegral
  apply integral_congr_ae
  filter_upwards [] with t
  ring

end HVRFallbackApplications
