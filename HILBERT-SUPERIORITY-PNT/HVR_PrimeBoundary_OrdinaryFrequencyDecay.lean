import HVR_PrimeBoundary_FourierDecay

noncomputable section
open Filter MeasureTheory HVRPrimeBoundaryFourierDecay HVRSmoothingBoundaryExtension
open scoped Topology

/-! Candidate conversion between the two Fourier conventions used by the
project. This proves decay of the actual boundary expression written in the
ordinary-frequency convention of the Abel/Fubini formula. It does not identify
this expression with an undamped prime-density convolution. No Lean was run
locally; external build and theorem-level audits are required. -/
namespace HVRPrimeBoundaryOrdinaryFrequencyDecay

def ordinaryBoundary (ψ : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ t : ℝ, (ψ t * Complex.exp ((t : ℂ) * Complex.I * (x : ℂ))) *
    patchedShift ((t : ℂ) * Complex.I)

/-- Exact sign and 2π conversion from the ordinary exponential convention to
the convention used in the audited Riemann–Lebesgue theorem. -/
theorem ordinaryBoundary_eq_scaled_fourier (ψ : ℝ → ℂ) (x : ℝ) :
    ordinaryBoundary ψ x = ∫ t : ℝ,
      Real.fourierChar (-(t * (x * (-(2 * Real.pi)⁻¹)))) • weightedBoundary ψ t := by
  unfold ordinaryBoundary
  apply integral_congr_ae
  filter_upwards [] with t
  have hp : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hz : 2 * Real.pi * (-(t * (x * (-(2 * Real.pi)⁻¹)))) = t * x := by
    field_simp
  rw [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul, hz, Complex.ofReal_mul]
  unfold weightedBoundary
  have he : ((t : ℂ) * (x : ℂ)) * Complex.I =
      (t : ℂ) * Complex.I * (x : ℂ) := by ring
  rw [he]
  ring

/-- The ordinary-frequency boundary integral tends to zero as x increases. -/
theorem ordinaryBoundary_tendsto_zero (ψ : ℝ → ℂ)
    (hψ : Continuous ψ) (hcompact : HasCompactSupport ψ) :
    Tendsto (ordinaryBoundary ψ) atTop (𝓝 0) := by
  exact HVRActualBoundaryFourier.ordinaryBoundary_tendsto_zero ψ hψ hcompact

end HVRPrimeBoundaryOrdinaryFrequencyDecay
