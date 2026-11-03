import HVRFourierPhase
import HVRCompactTranslation
import HVRFourierLimit
import HVROrdinaryFourier
import Mathlib.Tactic

/-!
Candidate closure of the two-sided Fourier-decay statement for continuous,
compactly supported complex-valued functions. The two substantive inputs are
HVRFourierPhase and HVRCompactTranslation, and the filter-generic squeeze
is HVRFourierLimit. The weighted-boundary adapter is abstract: instantiating
it for the actual PNT patched zeta boundary is a separate integration step.
No proof in this file may be promoted before matching external Lean build and
named-theorem axiom audit. Transitive target independence remains unverified.
-/
noncomputable section
open Filter MeasureTheory NativeFourierDecay
open scoped Topology

namespace HVRCompactFourierDecay

/-- The half-period approaches zero along positive frequencies. -/
theorem halfPeriod_tendsto_atTop : Tendsto halfPeriod atTop (𝓝 0) := by
  have hmul : Tendsto (fun ξ : ℝ => 2 * ξ) atTop atTop :=
    (Filter.tendsto_const_mul_atTop_of_pos (show (0 : ℝ) < 2 by norm_num)).2 tendsto_id
  simpa only [halfPeriod] using hmul.inv_tendsto_atTop

/-- The half-period approaches zero also along negative frequencies. -/
theorem halfPeriod_tendsto_atBot : Tendsto halfPeriod atBot (𝓝 0) := by
  have hmul : Tendsto (fun ξ : ℝ => 2 * ξ) atBot atBot :=
    (Filter.tendsto_const_mul_atBot_of_pos (show (0 : ℝ) < 2 by norm_num)).2 tendsto_id
  simpa only [halfPeriod] using hmul.inv_tendsto_atBot

/-- Positive-frequency decay for a continuous compactly supported function. -/
theorem fourier_tendsto_atTop (g : ℝ → ℂ) (hg : Continuous g)
    (hcompact : HasCompactSupport g) :
    Tendsto (integralTransform g) atTop (𝓝 0) := by
  apply HVRFourierLimit.decay_of_half_period_obligations g atTop
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with ξ hξ
    exact HVRFourierPhase.half_period_cancellation g
      (hg.integrable_of_hasCompactSupport hcompact) (ne_of_gt hξ)
  · have ht := (HVRCompactTranslation.translation_integral_tendsto g hg hcompact).comp
      halfPeriod_tendsto_atTop
    simpa only [translationDifference, Function.comp_def] using ht

/-- Negative-frequency decay for a continuous compactly supported function. -/
theorem fourier_tendsto_atBot (g : ℝ → ℂ) (hg : Continuous g)
    (hcompact : HasCompactSupport g) :
    Tendsto (integralTransform g) atBot (𝓝 0) := by
  apply HVRFourierLimit.decay_of_half_period_obligations g atBot
  · filter_upwards [eventually_lt_atBot (0 : ℝ)] with ξ hξ
    exact HVRFourierPhase.half_period_cancellation g
      (hg.integrable_of_hasCompactSupport hcompact) (ne_of_lt hξ)
  · have ht := (HVRCompactTranslation.translation_integral_tendsto g hg hcompact).comp
      halfPeriod_tendsto_atBot
    simpa only [translationDifference, Function.comp_def] using ht

/-- The ordinary convention requires negative-frequency decay in the 2π convention. -/
theorem ordinary_tendsto_atTop (g : ℝ → ℂ) (hg : Continuous g)
    (hcompact : HasCompactSupport g) :
    Tendsto (HVROrdinaryFourier.ordinaryIntegral g) atTop (𝓝 0) :=
  HVROrdinaryFourier.ordinaryIntegral_tendsto_zero_of_atBot g
    (fourier_tendsto_atBot g hg hcompact)

/-- Weighted-boundary form; b can subsequently be instantiated with the
actual continuous PNT boundary without importing the old Fourier theorem. -/
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

end HVRCompactFourierDecay
