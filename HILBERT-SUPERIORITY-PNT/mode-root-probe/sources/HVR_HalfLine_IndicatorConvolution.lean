import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal

/-! Candidate indicator-convolution limit. An integrable kernel with total
mass one has its convolution with 1_[0,infty) converging to one at +infty.
No positivity or compact support of the kernel is needed. This does not
construct the band-limited kernel or prove a Fourier identity or PNT.
The cumulative integral proof uses nonnegative lower-integral exhaustion;
matching external cached Lean and root-level axiom audit are required. -/
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
  have hcover : AECover volume atTop (fun x : ℝ => Set.Iic x) := by
    simpa only [Function.id_def] using
      (aecover_Iic (μ := volume) (b := fun x : ℝ => x) tendsto_id)
  have hkfin : (∫⁻ t : ℝ, ENNReal.ofReal ‖k t‖ ∂volume) < ⊤ :=
    (hasFiniteIntegral_iff_norm k).mp hk.2
  have hposfin : (∫⁻ t : ℝ, ENNReal.ofReal (k t) ∂volume) < ⊤ := by
    apply lt_of_le_of_lt ?_ hkfin
    apply lintegral_mono
    intro t
    apply ENNReal.ofReal_le_ofReal
    simpa only [Real.norm_eq_abs] using (le_abs_self (k t))
  have hnegfin : (∫⁻ t : ℝ, ENNReal.ofReal (-k t) ∂volume) < ⊤ := by
    apply lt_of_le_of_lt ?_ hkfin
    apply lintegral_mono
    intro t
    apply ENNReal.ofReal_le_ofReal
    simpa only [Real.norm_eq_abs, abs_neg] using (le_abs_self (-k t))
  have hpos : AEMeasurable (fun t : ℝ => ENNReal.ofReal (k t)) volume :=
    ENNReal.measurable_ofReal.comp_aemeasurable hk.aestronglyMeasurable.aemeasurable
  have hneg : AEMeasurable (fun t : ℝ => ENNReal.ofReal (-k t)) volume :=
    ENNReal.measurable_ofReal.comp_aemeasurable hk.aestronglyMeasurable.aemeasurable.neg
  have hpl := hcover.lintegral_tendsto_of_countably_generated hpos
  have hnl := hcover.lintegral_tendsto_of_countably_generated hneg
  have hp := (ENNReal.tendsto_toReal (ne_of_lt hposfin)).comp hpl
  have hn := (ENNReal.tendsto_toReal (ne_of_lt hnegfin)).comp hnl
  have hsub := hp.sub hn
  have hpoint (x : ℝ) :
      (∫ t : ℝ in Set.Iic x, k t) =
        (∫⁻ t : ℝ in Set.Iic x, ENNReal.ofReal (k t)).toReal -
          (∫⁻ t : ℝ in Set.Iic x, ENNReal.ofReal (-k t)).toReal := by
    exact integral_eq_lintegral_pos_part_sub_lintegral_neg_part
      (hk.mono_measure Measure.restrict_le_self)
  have hwhole : (∫ t : ℝ, k t) =
      (∫⁻ t : ℝ, ENNReal.ofReal (k t)).toReal -
        (∫⁻ t : ℝ, ENNReal.ofReal (-k t)).toReal :=
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part hk
  rw [hwhole]
  have hfun : (fun x : ℝ => ∫ t : ℝ in Set.Iic x, k t) =
      fun x : ℝ => (∫⁻ t : ℝ in Set.Iic x, ENNReal.ofReal (k t)).toReal -
        (∫⁻ t : ℝ in Set.Iic x, ENNReal.ofReal (-k t)).toReal := funext hpoint
  rw [hfun]
  simpa only [Function.comp_def] using hsub

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
