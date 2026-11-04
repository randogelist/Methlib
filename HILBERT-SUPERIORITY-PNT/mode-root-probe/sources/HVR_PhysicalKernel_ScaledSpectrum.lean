import HVR_SpectralCorrelation_Regularity
import HVR_PhysicalKernel_PositiveMass
import Mathlib.Tactic

noncomputable section
open MeasureTheory HVRPhysicalKernelCandidate HVRSpectralSeedCorrelation
open HVRSpectralCorrelationRegularity

/-!
Candidate ordinary-frequency test for the scaled and translated normalized
physical kernel. This file constructs the explicit spectral test and proves
its compact support and integrability for positive scale. The Fourier integral
identification with the physical kernel requires a separate change-of-variables
and Fourier identity, and is not asserted here. No local Lean execution.
-/
namespace HVRPhysicalKernelScaledSpectrum

/-- Proposed ordinary-frequency test, with the 2π factor and translation phase. -/
def scaledSpectrum (w : ℝ) (hw : 0 < w) (N c t : ℝ) : ℂ :=
  (((2 * Real.pi * mass w hw : ℝ) : ℂ)⁻¹) *
    Complex.exp (-(t : ℂ) * Complex.I * (c : ℂ)) *
      (correlation w hw (t / (2 * Real.pi * N)) : ℂ)

/-- The proposed test is continuous in the frequency variable. -/
theorem scaledSpectrum_continuous (w : ℝ) (hw : 0 < w) (N c : ℝ) :
    Continuous (scaledSpectrum w hw N c) := by
  have he : Continuous (fun t : ℝ => Complex.exp (-(t : ℂ) * Complex.I * (c : ℂ))) := by
    fun_prop
  have ht : Continuous (fun t : ℝ => t / (2 * Real.pi * N)) := by fun_prop
  have hc : Continuous (fun t : ℝ => (correlation w hw (t / (2 * Real.pi * N)) : ℂ)) :=
    Complex.continuous_ofReal.comp ((correlation_continuous w hw).comp ht)
  change Continuous (fun t : ℝ => (((2 * Real.pi * mass w hw : ℝ) : ℂ)⁻¹) *
    Complex.exp (-(t : ℂ) * Complex.I * (c : ℂ)) *
      (correlation w hw (t / (2 * Real.pi * N)) : ℂ))
  exact (continuous_const.mul he).mul hc

/-- Dilation enlarges the ordinary-frequency band to 2π N w. -/
theorem scaledSpectrum_zero_of_band (w : ℝ) (hw : 0 < w) (N c t : ℝ)
    (hN : 0 < N) (ht : 2 * Real.pi * N * w ≤ |t|) :
    scaledSpectrum w hw N c t = 0 := by
  have hp : 0 < 2 * Real.pi * N := by positivity
  have hle : w * (2 * Real.pi * N) ≤ |t| := by nlinarith
  have hband : w ≤ |t / (2 * Real.pi * N)| := by
    rw [abs_div, abs_of_pos hp, le_div_iff₀ hp]
    exact hle
  rw [scaledSpectrum, correlation_zero_of_band w hw _ hband]
  simp

/-- This concrete scaled spectrum has compact support. -/
theorem scaledSpectrum_compact (w : ℝ) (hw : 0 < w) (N c : ℝ) (hN : 0 < N) :
    HasCompactSupport (scaledSpectrum w hw N c) := by
  apply HasCompactSupport.intro (K := Set.Icc (-(2 * Real.pi * N * w)) (2 * Real.pi * N * w)) isCompact_Icc
  intro t ht
  apply scaledSpectrum_zero_of_band w hw N c t hN
  by_contra hn
  have habs : |t| < 2 * Real.pi * N * w := lt_of_not_ge hn
  have ht' : t ∈ Set.Icc (-(2 * Real.pi * N * w)) (2 * Real.pi * N * w) := by
    exact ⟨le_of_lt (abs_lt.mp habs).1, le_of_lt (abs_lt.mp habs).2⟩
  exact ht ht'

/-- The proposed frequency test is L1, as required by the compact Abel glue. -/
theorem scaledSpectrum_integrable (w : ℝ) (hw : 0 < w) (N c : ℝ) (hN : 0 < N) :
    Integrable (scaledSpectrum w hw N c) volume :=
  (scaledSpectrum_continuous w hw N c).integrable_of_hasCompactSupport
    (scaledSpectrum_compact w hw N c hN)

end HVRPhysicalKernelScaledSpectrum
