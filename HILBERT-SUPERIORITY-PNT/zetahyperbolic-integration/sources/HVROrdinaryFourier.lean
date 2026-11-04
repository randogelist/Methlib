import NativeFourierDecay
import Mathlib.Tactic

/-!
Bridge from the audited HVR Fourier convention to the ordinary-frequency
integral. The boundary function itself is a parameter, so this file does not
import the original PNT Fourier-decay theorem. No target-independence claim.
-/

noncomputable section
open Filter MeasureTheory NativeFourierDecay
open scoped Topology

namespace HVROrdinaryFourier

/-- Fourier integral in the project's ordinary exponential convention. -/
def ordinaryIntegral (g : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ t : ℝ, Complex.exp ((t : ℂ) * Complex.I * (x : ℂ)) * g t

/-- Conversion of ordinary frequency to the 2π Fourier convention. -/
theorem ordinaryIntegral_eq_scaled (g : ℝ → ℂ) (x : ℝ) :
    ordinaryIntegral g x = integralTransform g (x * (-(2 * Real.pi)⁻¹)) := by
  unfold ordinaryIntegral integralTransform
  apply integral_congr_ae
  filter_upwards [] with t
  have hp : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hz : (2 * Real.pi : ℝ) * (-(t * (x * (-(2 * Real.pi)⁻¹)))) = t * x := by
    field_simp
  rw [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul, hz, Complex.ofReal_mul]
  have he : ((t : ℂ) * (x : ℂ)) * Complex.I =
      (t : ℂ) * Complex.I * (x : ℂ) := by ring
  rw [he]

/-- Decay at negative Fourier frequency supplies ordinary-frequency decay. -/
theorem ordinaryIntegral_tendsto_zero_of_atBot (g : ℝ → ℂ)
    (hfreq : Tendsto (integralTransform g) atBot (𝓝 0)) :
    Tendsto (ordinaryIntegral g) atTop (𝓝 0) := by
  have hscale : Tendsto (fun x : ℝ => x * (-(2 * Real.pi)⁻¹)) atTop atBot := by
    have hc : -(2 * Real.pi)⁻¹ < (0 : ℝ) :=
      neg_lt_zero.mpr (inv_pos.mpr (mul_pos (by norm_num) Real.pi_pos))
    apply (Filter.tendsto_mul_const_atBot_of_neg hc).2
    exact tendsto_id
  have hscaled := hfreq.comp hscale
  apply hscaled.congr'
  filter_upwards [] with x
  exact (ordinaryIntegral_eq_scaled g x).symm

end HVROrdinaryFourier
