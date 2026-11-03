import HVR_PrimeDensity_ScaledSpectrumDecay
import Mathlib.MeasureTheory.Group.Integral

noncomputable section
open Filter MeasureTheory
open scoped Topology
open HVRPhysicalKernelScaledSpectrum HVRPrimeBoundaryCompactGlue
open HVRPrimeDensityFubiniBridge HVRPrimeDensitySpatialAbel

/-! Candidate frequency reflection for the opposite smoothing direction.
The kernel identity uses the ordinary-frequency convention. Integrability of
its original inverse transform remains explicit; matching that transform to
the actual physical kernel is a separate obligation. No local Lean run. -/
namespace HVRPrimeDensityReflectedSpectrum

def reflectFrequency (ψ : ℝ → ℂ) (t : ℝ) : ℂ := ψ (-t)

/-- Reflecting the frequency test reflects the inverse kernel. -/
theorem kernel_reflectFrequency (ψ : ℝ → ℂ) (x : ℝ) :
    kernel (reflectFrequency ψ) x = kernel ψ (-x) := by
  unfold kernel reflectFrequency
  calc
    (∫ t : ℝ, ψ (-t) * Complex.exp ((t : ℂ) * Complex.I * (x : ℂ))) =
        ∫ t : ℝ, ψ (-t) * Complex.exp (((-t : ℝ) : ℂ) * Complex.I * ((-x : ℝ) : ℂ)) := by
      apply integral_congr_ae
      filter_upwards [] with t
      have heq : (t : ℂ) * Complex.I * (x : ℂ) =
          (((-t : ℝ) : ℂ) * Complex.I * ((-x : ℝ) : ℂ)) := by
        push_cast
        ring
      rw [heq]
    _ = ∫ t : ℝ, ψ t * Complex.exp ((t : ℂ) * Complex.I * ((-x : ℝ) : ℂ)) :=
      integral_neg_eq_self (fun t : ℝ => ψ t * Complex.exp ((t : ℂ) * Complex.I * ((-x : ℝ) : ℂ))) volume

/-- The reflected scaled spectrum is supported in the same symmetric band. -/
theorem reflectedScaledSpectrum_zero_of_band (w : ℝ) (hw : 0 < w) (N c t : ℝ)
    (hN : 0 < N) (ht : 2 * Real.pi * N * w ≤ |t|) :
    reflectFrequency (scaledSpectrum w hw N c) t = 0 := by
  apply scaledSpectrum_zero_of_band w hw N c (-t) hN
  simpa only [abs_neg] using ht

theorem reflectedScaledSpectrum_compact (w : ℝ) (hw : 0 < w) (N c : ℝ) (hN : 0 < N) :
    HasCompactSupport (reflectFrequency (scaledSpectrum w hw N c)) := by
  apply HasCompactSupport.intro (K := Set.Icc (-(2 * Real.pi * N * w)) (2 * Real.pi * N * w)) isCompact_Icc
  intro t ht
  apply reflectedScaledSpectrum_zero_of_band w hw N c t hN
  by_contra hn
  have ha : |t| < 2 * Real.pi * N * w := lt_of_not_ge hn
  exact ht ⟨le_of_lt (abs_lt.mp ha).1, le_of_lt (abs_lt.mp ha).2⟩

/-- Opposite-direction actual prime-error convolution tends to zero, assuming
integrability of the original inverse kernel. -/
theorem reflected_scaledSpectrum_undamped_tendsto_zero
    (w : ℝ) (hw : 0 < w) (N c : ℝ) (hN : 0 < N)
    (hkernel : Integrable (kernel (scaledSpectrum w hw N c)) volume) :
    Tendsto (undamped (kernel (reflectFrequency (scaledSpectrum w hw N c)))) atTop (𝓝 0) := by
  let ψ := scaledSpectrum w hw N c
  let R : ℝ := 2 * Real.pi * N * w
  have hψ : Integrable (reflectFrequency ψ) volume := by
    change Integrable (fun t : ℝ => scaledSpectrum w hw N c (-t)) volume
    exact (scaledSpectrum_integrable w hw N c hN).comp_neg
  have hcont : Continuous (reflectFrequency ψ) := by
    change Continuous (fun t : ℝ => scaledSpectrum w hw N c (-t))
    exact (scaledSpectrum_continuous w hw N c).comp continuous_neg
  have hkr : Integrable (kernel (reflectFrequency ψ)) volume := by
    have heq : kernel (reflectFrequency ψ) = fun x : ℝ => kernel ψ (-x) := by
      funext x
      exact kernel_reflectFrequency ψ x
    rw [heq]
    exact hkernel.comp_neg
  have hs : ∀ t : ℝ, reflectFrequency ψ t ≠ 0 → t ∈ Set.Icc (-R) R := by
    intro t ht
    by_contra hn
    have hband : R ≤ |t| := by
      by_contra hb
      have ha : |t| < R := lt_of_not_ge hb
      exact hn ⟨le_of_lt (abs_lt.mp ha).1, le_of_lt (abs_lt.mp ha).2⟩
    apply ht
    exact reflectedScaledSpectrum_zero_of_band w hw N c t hN hband
  exact undamped_tendsto_zero_of_compact (reflectFrequency ψ)
    (Set.Icc (-R) R) isCompact_Icc hs hψ hkr hcont
    (reflectedScaledSpectrum_compact w hw N c hN)

end HVRPrimeDensityReflectedSpectrum
