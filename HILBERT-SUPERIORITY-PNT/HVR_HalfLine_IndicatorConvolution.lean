import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

noncomputable section
open MeasureTheory Filter Set
open scoped Topology

/-! Candidate indicator-convolution limit. An integrable kernel with total
mass one has its convolution with 1_[0,infty) converging to one at +infty.
No positivity or compact support of the kernel is needed. This does not
construct the band-limited kernel or prove a Fourier identity or PNT.
The exact pinned-cache APIs and named theorem audits require external Lean.
No Lean execution was performed locally. -/
namespace HVRHalfLineIndicatorConvolution

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
  have hlim : Tendsto (fun x : ℝ => ∫ t : ℝ, (Set.Iic x).indicator k t)
      atTop (𝓝 (∫ t : ℝ, k t)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun t : ℝ => ‖k t‖)
    · exact Filter.Eventually.of_forall fun x => hk.aestronglyMeasurable.indicator measurableSet_Iic
    · exact Filter.Eventually.of_forall fun x => Filter.Eventually.of_forall fun t =>
        norm_indicator_le_norm_self _ _
    · exact hk.norm
    · apply Filter.Eventually.of_forall
      intro t
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop t] with x hx
      simp only [Set.indicator_of_mem (show t ∈ Set.Iic x from hx)]
  simpa only [integral_indicator measurableSet_Iic] using hlim

/-- A normalized integrable kernel smooths the positive half-line indicator
into a function tending to one at positive infinity. -/
theorem halfLineConvolution_tendsto_one (k : ℝ → ℝ)
    (hk : Integrable k volume) (hunit : (∫ t : ℝ, k t) = 1) :
    Tendsto (halfLineConvolution k) atTop (𝓝 1) := by
  have hfun : halfLineConvolution k = (fun x : ℝ => ∫ t : ℝ in Set.Iic x, k t) :=
    funext (halfLineConvolution_eq_integral_Iic k)
  rw [hfun, ← hunit]
  exact integral_Iic_tendsto_integral k hk

end HVRHalfLineIndicatorConvolution
