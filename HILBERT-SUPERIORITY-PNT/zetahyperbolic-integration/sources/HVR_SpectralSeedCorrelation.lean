import HVR_PhysicalKernel_Candidate
import Mathlib.Tactic

noncomputable section
open MeasureTheory HVRSmoothingFrequencySeed

/-! Candidate support fact for the frequency autocorrelation. It does not
identify its inverse Fourier transform with the physical square, nor prove
any PNT assertion. No local Lean execution. -/
namespace HVRSpectralSeedCorrelation

def correlation (w : ℝ) (hw : 0 < w) (t : ℝ) : ℝ :=
  ∫ u : ℝ, seed w hw u * seed w hw (u - t)

theorem correlation_nonneg (w : ℝ) (hw : 0 < w) (t : ℝ) :
    0 ≤ correlation w hw t := by
  unfold correlation
  apply integral_nonneg
  intro u
  exact mul_nonneg (seed_nonneg w hw u) (seed_nonneg w hw (u - t))

theorem correlation_zero_of_band (w : ℝ) (hw : 0 < w) (t : ℝ)
    (ht : w ≤ |t|) : correlation w hw t = 0 := by
  have hzero : (fun u : ℝ => seed w hw u * seed w hw (u - t)) =
      (fun _ : ℝ => (0 : ℝ)) := by
    funext u
    by_cases hu : w / 2 ≤ |u|
    · rw [seed_zero_of_band w hw u hu, zero_mul]
    · have hu' : |u| < w / 2 := lt_of_not_ge hu
      have huv : w / 2 ≤ |u - t| := by
        by_contra hn
        have hv' : |u - t| < w / 2 := lt_of_not_ge hn
        have hu_bounds := abs_lt.mp hu'
        have hv_bounds := abs_lt.mp hv'
        have ht_bounds : -w < t ∧ t < w := by constructor <;> linarith
        have ht' : |t| < w := abs_lt.mpr ht_bounds
        linarith
      rw [seed_zero_of_band w hw (u - t) huv, mul_zero]
  unfold correlation
  rw [hzero]
  simp

end HVRSpectralSeedCorrelation
