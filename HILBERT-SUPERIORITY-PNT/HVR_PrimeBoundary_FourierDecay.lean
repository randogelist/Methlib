import HVR_Smoothing_BoundaryExtension
import HVRActualBoundaryFourier

noncomputable section
open Filter MeasureTheory HVRSmoothingBoundaryExtension
open scoped Topology

/-!
Candidate Fourier decay for the actual analytic boundary expression. The
frequency weight is an arbitrary continuous compactly supported complex
function. The Riemann–Lebesgue integral is a frequency-side object: this file
does NOT claim it equals any convolution of the prime-count error. Establishing
that identity using kernel Fourier inversion and Fubini, the construction of
the needed nonnegative kernel, and PNT remain separate obligations. The
Mathlib Fourier convention contains 2*pi in Real.fourierChar. Its pinned-cache
API and all transitive proof dependencies require external validation.
No Lean run was performed locally.
-/
namespace HVRPrimeBoundaryFourierDecay

/-- A compact frequency test against the actual continuous boundary germ. -/
def weightedBoundary (ψ : ℝ → ℂ) (t : ℝ) : ℂ :=
  ψ t * patchedShift ((t : ℂ) * Complex.I)

theorem weightedBoundary_continuous (ψ : ℝ → ℂ) (hψ : Continuous ψ) :
    Continuous (weightedBoundary ψ) := by
  exact hψ.mul patchedShift_continuous_boundary

theorem weightedBoundary_hasCompactSupport (ψ : ℝ → ℂ)
    (hψ : HasCompactSupport ψ) : HasCompactSupport (weightedBoundary ψ) := by
  exact hψ.mul_right

/-- The boundary frequency expression is a genuine L1 function, so its
Fourier integral is not a vacuous value from non-integrability. -/
theorem weightedBoundary_integrable (ψ : ℝ → ℂ) (hψ : Continuous ψ)
    (hcompact : HasCompactSupport ψ) : Integrable (weightedBoundary ψ) volume := by
  exact (weightedBoundary_continuous ψ hψ).integrable_of_hasCompactSupport
    (weightedBoundary_hasCompactSupport ψ hcompact)

/-- The Fourier transform of the actual boundary germ times a compact
frequency test tends to zero at +infinity. This is the frequency-side limit
only; no equality with a smoothed prime-count function is claimed. -/
theorem weightedBoundary_fourier_tendsto_zero (ψ : ℝ → ℂ)
    (hψ : Continuous ψ) (hcompact : HasCompactSupport ψ) :
    Integrable (weightedBoundary ψ) volume ∧
    Tendsto (fun x : ℝ =>
      ∫ t : ℝ, Real.fourierChar (-(t * x)) • weightedBoundary ψ t)
      atTop (𝓝 0) := by
  exact HVRActualBoundaryFourier.weightedBoundary_fourier_tendsto_zero ψ hψ hcompact

end HVRPrimeBoundaryFourierDecay
