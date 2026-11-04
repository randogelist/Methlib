import HVRRealReflection
import HVR_PrimeDensity_FubiniIntegrable
import HVR_PrimeDensity_WeightedIntegrability
import HVR_Correction_BoundaryLimit
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section
open MeasureTheory

local instance : (volume : Measure ℝ).IsNegInvariant :=
  HVRRealReflection.real_volume_negInvariant_direct
open Filter MeasureTheory HVRPrimeLogDensity HVRPrimeDensityFubiniBridge
open HVRPrimeDensityWeightedIntegrability HVRCorrectionBoundaryLimit
open scoped Topology

/-!
Candidate spatial dominated-convergence step for the actual prime density.
For an arbitrary complex integrable kernel, positive reciprocal damping can
be removed in the half-line convolution. No frequency-side limit, spectral
support, kernel concentration, PNT, or dependency-independence is asserted.
This file has not been compiled or audited. No Lean was run locally.
-/
namespace HVRPrimeDensitySpatialAbel

/-- The undamped actual prime-density error convolved on the positive half-line. -/
def undamped (K : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ u : ℝ in Set.Ioi 0, ((logPrimeDensity u : ℂ) - 1) * K (x - u)

/-- Remove positive reciprocal Abel damping under the spatial integral. -/
theorem spatial_abel_tendsto (K : ℝ → ℂ) (hK : Integrable K volume) (x : ℝ) :
    Tendsto (fun n : ℕ => ∫ u : ℝ in Set.Ioi 0,
      dampedError (boundaryEps n) u * K (x - u)) atTop (𝓝 (undamped K x)) := by
  have hshift : Integrable (fun u : ℝ => K (x - u)) volume := hK.comp_sub_left x
  have hshift' : IntegrableOn (fun u : ℝ => K (x - u)) (Set.Ioi 0) volume :=
    hshift.mono_measure Measure.restrict_le_self
  have hden : Measurable (fun u : ℝ => (logPrimeDensity u : ℂ) - 1) := by
    exact (Complex.continuous_ofReal.measurable.comp logPrimeDensity_measurable).sub measurable_const
  unfold undamped
  apply tendsto_integral_filter_of_dominated_convergence
    (fun u : ℝ => (Real.log 4 + 1) * ‖K (x - u)‖)
  · filter_upwards [] with n
    have hexp : Continuous (fun u : ℝ => Complex.exp (-(boundaryEps n : ℂ) * (u : ℂ))) := by
      fun_prop
    exact ((hden.aestronglyMeasurable.mul hexp.measurable.aestronglyMeasurable).mul
      hshift'.aestronglyMeasurable)
  · filter_upwards [] with n
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : (0 : ℝ) < u := hu
    have hu' : 0 ≤ u := le_of_lt hu0
    have ha : 0 ≤ boundaryEps n := le_of_lt (boundaryEps_pos n)
    have hnormden : ‖(logPrimeDensity u : ℂ) - 1‖ ≤ Real.log 4 + 1 := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      apply abs_le.mpr
      constructor
      · have hlog : 0 ≤ Real.log 4 := by positivity
        linarith [logPrimeDensity_nonneg u]
      · linarith [logPrimeDensity_le_log_four u]
    have hnormexp : ‖Complex.exp (-(boundaryEps n : ℂ) * (u : ℂ))‖ ≤ 1 := by
      rw [Complex.norm_exp]
      apply Real.exp_le_one_iff.mpr
      simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im,
        Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      nlinarith
    have hprod : ‖(logPrimeDensity u : ℂ) - 1‖ *
        ‖Complex.exp (-(boundaryEps n : ℂ) * (u : ℂ))‖ ≤ Real.log 4 + 1 := by
      calc
        _ ≤ ‖(logPrimeDensity u : ℂ) - 1‖ :=
          mul_le_of_le_one_right (norm_nonneg _) hnormexp
        _ ≤ _ := hnormden
    simp only [dampedError, norm_mul]
    exact mul_le_mul_of_nonneg_right hprod (norm_nonneg _)
  · exact (hshift'.norm.const_mul (Real.log 4 + 1))
  · filter_upwards [] with u
    have he : Tendsto (fun n : ℕ => Complex.exp (-(boundaryEps n : ℂ) * (u : ℂ)))
        atTop (𝓝 1) := by
      have hc : ContinuousAt (fun a : ℝ => Complex.exp (-(a : ℂ) * (u : ℂ))) 0 := by
        fun_prop
      simpa only [Function.comp_def, Complex.ofReal_zero, neg_zero, zero_mul, Complex.exp_zero] using
        hc.tendsto.comp boundaryEps_tendsto
    simpa only [dampedError, mul_one] using
      ((tendsto_const_nhds.mul he).mul tendsto_const_nhds)

end HVRPrimeDensitySpatialAbel
