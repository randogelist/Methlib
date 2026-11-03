import HVRSpatialTail
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

noncomputable section
open MeasureTheory Filter Set
open scoped Topology

/-! Candidate indicator-convolution limit. An integrable kernel with total
mass one has its convolution with 1_[0,infty) converging to one at +infty.
No positivity or compact support of the kernel is needed. This does not
construct the band-limited kernel or prove a Fourier identity or PNT.
This rebuild uses HVRSpatialTail and does not directly call either old dominated
convergence endpoint. Transitive dependency coverage is not verified.
This source is an uncompiled candidate; no Lean was executed locally. -/
namespace HVRNativeHalfLineIndicatorConvolution

/-- Convolution of a real kernel with the positive half-line indicator. -/
def halfLineConvolution (k : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ t : ℝ, k t * (Set.Ici (0 : ℝ)).indicator (fun _ : ℝ => (1 : ℝ)) (x - t)

/-- The convolution equals the cumulative integral of the kernel. -/
theorem halfLineConvolution_eq_integral_Iic (k : ℝ → ℝ) (x : ℝ) :
    halfLineConvolution k x = ∫ t : ℝ in Set.Iic x, k t := by
  unfold halfLineConvolution
  rw [← integral_indicator measurableSet_Iic]
  apply integral_congr_ae
  filter_upwards [] with t
  by_cases h : t ≤ x
  · have hsub : (0 : ℝ) ≤ x - t := sub_nonneg.mpr h
    simp only [Set.indicator_of_mem (show x - t ∈ Set.Ici (0 : ℝ) from hsub),
      Set.indicator_of_mem (show t ∈ Set.Iic x from h), mul_one]
  · have hsub : ¬ (0 : ℝ) ≤ x - t := by
      intro hz
      exact h (sub_nonneg.mp hz)
    have hnot : x - t ∉ Set.Ici (0 : ℝ) := hsub
    have hnot' : t ∉ Set.Iic x := h
    simp only [Set.indicator_of_notMem hnot, Set.indicator_of_notMem hnot', mul_zero]

/-- Cumulative integrals of an integrable kernel exhaust its total integral. -/
theorem integral_Iic_tendsto_integral (k : ℝ → ℝ) (hk : Integrable k volume) :
    Tendsto (fun x : ℝ => ∫ t : ℝ in Set.Iic x, k t) atTop (𝓝 (∫ t : ℝ, k t)) := by
  exact HVRSpatialTail.cumulative_integral_tendsto_total k hk

/-- A normalized integrable kernel smooths the positive half-line indicator
into a function tending to one at positive infinity. -/
theorem halfLineConvolution_tendsto_one (k : ℝ → ℝ)
    (hk : Integrable k volume) (hunit : (∫ t : ℝ, k t) = 1) :
    Tendsto (halfLineConvolution k) atTop (𝓝 1) := by
  have hfun : halfLineConvolution k = (fun x : ℝ => ∫ t : ℝ in Set.Iic x, k t) :=
    funext (halfLineConvolution_eq_integral_Iic k)
  rw [hfun, ← hunit]
  exact integral_Iic_tendsto_integral k hk

end HVRNativeHalfLineIndicatorConvolution
