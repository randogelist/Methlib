import HVRNativeHalfLineTail
import Mathlib.Tactic

/-!
Actual half-line indicator-convolution application from the PNT construction.
The definition and conclusion match the existing project module, while the
tail limit is proved through HVRNativeHalfLineTail's monotone-lintegral route.
A separate adapter must identify this definition with the original project
definition before substitution into the original PNT root. No target-freedom
or compiler status is asserted until external checks are complete.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace HVRNativeHalfLineApplication

def halfLineConvolution (k : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ t : ℝ, k t * (Set.Ici (0 : ℝ)).indicator (fun _ : ℝ => (1 : ℝ)) (x - t)

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

theorem halfLineConvolution_tendsto_one (k : ℝ → ℝ)
    (hk : Integrable k volume) (hunit : (∫ t : ℝ, k t) = 1) :
    Tendsto (halfLineConvolution k) atTop (𝓝 1) := by
  have hfun : halfLineConvolution k = (fun x : ℝ => ∫ t : ℝ in Set.Iic x, k t) :=
    funext (halfLineConvolution_eq_integral_Iic k)
  rw [hfun, ← hunit]
  exact HVRNativeHalfLineTail.integral_Iic_tendsto_integral k hk

end HVRNativeHalfLineApplication
