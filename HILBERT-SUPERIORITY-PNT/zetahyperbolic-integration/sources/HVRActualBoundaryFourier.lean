import HVR_Smoothing_BoundaryExtension
import HVRCompactFourierDecay

/-!
Actual PNT boundary specialization of the HVR compact-support Fourier route.
This file defines its own weighted and ordinary boundary expressions with the
same bodies as the original PNT Fourier modules, without importing those
modules or naming Mathlib's Riemann-Lebesgue theorem. Its proof depends on
previous project boundary continuity and on HVRCompactFourierDecay. It does
not identify the boundary Fourier integral with a prime-density convolution.
This file is an uncompiled candidate; no dependency independence is claimed.
-/
noncomputable section
open Filter MeasureTheory HVRSmoothingBoundaryExtension NativeFourierDecay
open scoped Topology

namespace HVRActualBoundaryFourier

/-- Actual patched zeta boundary, weighted by the frequency test. -/
def weightedBoundary (ψ : ℝ → ℂ) (t : ℝ) : ℂ :=
  ψ t * patchedShift ((t : ℂ) * Complex.I)

/-- Actual PNT ordinary-frequency integral, with the original expression body. -/
def ordinaryBoundary (ψ : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ t : ℝ, (ψ t * Complex.exp ((t : ℂ) * Complex.I * (x : ℂ))) *
    patchedShift ((t : ℂ) * Complex.I)

theorem weightedBoundary_continuous (ψ : ℝ → ℂ) (hψ : Continuous ψ) :
    Continuous (weightedBoundary ψ) := by
  exact hψ.mul patchedShift_continuous_boundary

theorem weightedBoundary_hasCompactSupport (ψ : ℝ → ℂ)
    (hcompact : HasCompactSupport ψ) : HasCompactSupport (weightedBoundary ψ) := by
  exact hcompact.mul_right

/-- Same positive-frequency content as the original PNT Fourier decay result. -/
theorem weightedBoundary_fourier_tendsto_zero (ψ : ℝ → ℂ)
    (hψ : Continuous ψ) (hcompact : HasCompactSupport ψ) :
    Integrable (weightedBoundary ψ) volume ∧
    Tendsto (fun x : ℝ =>
      ∫ t : ℝ, Real.fourierChar (-(t * x)) • weightedBoundary ψ t)
      atTop (𝓝 0) := by
  refine ⟨(weightedBoundary_continuous ψ hψ).integrable_of_hasCompactSupport
    (weightedBoundary_hasCompactSupport ψ hcompact), ?_⟩
  exact HVRCompactFourierDecay.fourier_tendsto_atTop (weightedBoundary ψ)
    (weightedBoundary_continuous ψ hψ) (weightedBoundary_hasCompactSupport ψ hcompact)

/-- The original PNT ordinary-frequency endpoint using the HVR route. -/
theorem ordinaryBoundary_tendsto_zero (ψ : ℝ → ℂ)
    (hψ : Continuous ψ) (hcompact : HasCompactSupport ψ) :
    Tendsto (ordinaryBoundary ψ) atTop (𝓝 0) := by
  exact HVRCompactFourierDecay.weighted_boundary_tendsto_atTop ψ
    (fun t : ℝ => patchedShift ((t : ℂ) * Complex.I))
    hψ hcompact patchedShift_continuous_boundary

end HVRActualBoundaryFourier
