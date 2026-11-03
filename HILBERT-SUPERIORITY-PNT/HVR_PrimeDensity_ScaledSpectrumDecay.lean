import HVR_PhysicalKernel_ScaledSpectrum
import HVR_PrimeBoundary_CompactGlue

noncomputable section
open Filter MeasureTheory
open scoped Topology
open HVRPhysicalKernelScaledSpectrum HVRPrimeBoundaryCompactGlue
open HVRPrimeDensityFubiniBridge HVRPrimeDensitySpatialAbel

/-!
Candidate application of the compact-frequency Abel glue to the proposed
scaled spectrum of the actual physical kernel. Integrability of its inverse
kernel is an explicit assumption; this file does not identify that kernel with
scaledTranslate, and does not assert PNT. No local Lean execution.
-/
namespace HVRPrimeDensityScaledSpectrumDecay

/-- If the inverse transform is integrable, the actual prime error smoothed
with the explicit scaled frequency test tends to zero. -/
theorem scaledSpectrum_undamped_tendsto_zero
    (w : ℝ) (hw : 0 < w) (N c : ℝ) (hN : 0 < N)
    (hkernel : Integrable (kernel (scaledSpectrum w hw N c)) volume) :
    Tendsto (undamped (kernel (scaledSpectrum w hw N c))) atTop (𝓝 0) := by
  let R : ℝ := 2 * Real.pi * N * w
  have hK : IsCompact (Set.Icc (-R) R) := isCompact_Icc
  have hs : ∀ t : ℝ, scaledSpectrum w hw N c t ≠ 0 → t ∈ Set.Icc (-R) R := by
    intro t ht
    by_contra hn
    have hband : R ≤ |t| := by
      by_contra hb
      have ha : |t| < R := lt_of_not_ge hb
      exact hn ⟨le_of_lt (abs_lt.mp ha).1, le_of_lt (abs_lt.mp ha).2⟩
    apply ht
    exact scaledSpectrum_zero_of_band w hw N c t hN hband
  exact undamped_tendsto_zero_of_compact (scaledSpectrum w hw N c)
    (Set.Icc (-R) R) hK hs (scaledSpectrum_integrable w hw N c hN)
    hkernel (scaledSpectrum_continuous w hw N c) (scaledSpectrum_compact w hw N c hN)

end HVRPrimeDensityScaledSpectrumDecay
