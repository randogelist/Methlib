import HVR_Smoothing_BoundaryExtension
import HVRFallbackApplications

/-!
Actual PNT boundary specialization of the fallback compact-support route.
The fallback theorem adapts Mathlib's RiemannLebesgueLemma.lean,
Copyright (c) 2022 David Loeffler, Apache License 2.0. This is not an
independently discovered argument, and recursive target absence has not been
verified. It does not identify the boundary integral with a PNT convolution.
-/
noncomputable section
open Filter MeasureTheory HVRSmoothingBoundaryExtension NativeFourierDecay
open scoped Topology

namespace HVRFallbackActualBoundary

/-- The exact expression body from the original PNT weighted boundary. -/
def weightedBoundary (ψ : ℝ → ℂ) (t : ℝ) : ℂ :=
  ψ t * patchedShift ((t : ℂ) * Complex.I)

/-- The exact expression body from the original PNT ordinary boundary. -/
def ordinaryBoundary (ψ : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ t : ℝ, (ψ t * Complex.exp ((t : ℂ) * Complex.I * (x : ℂ))) *
    patchedShift ((t : ℂ) * Complex.I)

theorem weightedBoundary_continuous (ψ : ℝ → ℂ) (hψ : Continuous ψ) :
    Continuous (weightedBoundary ψ) := by
  exact hψ.mul patchedShift_continuous_boundary

theorem weightedBoundary_hasCompactSupport (ψ : ℝ → ℂ)
    (hcompact : HasCompactSupport ψ) : HasCompactSupport (weightedBoundary ψ) := by
  exact hcompact.mul_right

/-- Same positive-frequency statement as the original PNT module. -/
theorem weightedBoundary_fourier_tendsto_zero (ψ : ℝ → ℂ)
    (hψ : Continuous ψ) (hcompact : HasCompactSupport ψ) :
    Integrable (weightedBoundary ψ) volume ∧
    Tendsto (fun x : ℝ =>
      ∫ t : ℝ, Real.fourierChar (-(t * x)) • weightedBoundary ψ t)
      atTop (𝓝 0) := by
  refine ⟨(weightedBoundary_continuous ψ hψ).integrable_of_hasCompactSupport
    (weightedBoundary_hasCompactSupport ψ hcompact), ?_⟩
  exact HVRFallbackApplications.fourier_tendsto_atTop (weightedBoundary ψ)
    (weightedBoundary_continuous ψ hψ) (weightedBoundary_hasCompactSupport ψ hcompact)

/-- Same ordinary-frequency statement as the original PNT module. -/
theorem ordinaryBoundary_tendsto_zero (ψ : ℝ → ℂ)
    (hψ : Continuous ψ) (hcompact : HasCompactSupport ψ) :
    Tendsto (ordinaryBoundary ψ) atTop (𝓝 0) := by
  exact HVRFallbackApplications.weighted_boundary_tendsto_atTop ψ
    (fun t : ℝ => patchedShift ((t : ℂ) * Complex.I))
    hψ hcompact patchedShift_continuous_boundary

end HVRFallbackActualBoundary
