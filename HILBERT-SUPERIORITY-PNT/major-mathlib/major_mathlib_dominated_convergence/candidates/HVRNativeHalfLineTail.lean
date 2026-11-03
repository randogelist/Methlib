import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-!
The cumulative integral over Iic x exhausts the total integral as x tends to
infinity.  The proof splits a real-valued integrable function into its
nonnegative and negative parts, uses monotone lower-integral exhaustion, and
converts each finite extended-real limit to a real limit.  It does not invoke
`MeasureTheory.tendsto_integral_filter_of_dominated_convergence` or the
sequential `MeasureTheory.tendsto_integral_of_dominated_convergence` by name.
The monotone lower-integral exhaustion theorem and standard Bochner integral
infrastructure are Mathlib dependencies.  Neither compilation nor recursive
dependency absence is asserted in this uncompiled candidate.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace HVRNativeHalfLineTail

/-- For an integrable real function, cumulative integrals over the lower
half-line approach the full integral. -/
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

end HVRNativeHalfLineTail
