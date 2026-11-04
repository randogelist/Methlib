import HVRRealReflection
import HVR_PrimeDensity_FubiniIntegrable
import HVR_PrimeDensity_WeightedIntegrability
import HVR_Correction_BoundaryLimit
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Basic

noncomputable section
open MeasureTheory

local instance : (volume : Measure ℝ).IsNegInvariant :=
  HVRRealReflection.real_volume_negInvariant_direct
open Filter MeasureTheory HVRPrimeLogDensity HVRPrimeDensityFubiniBridge
open HVRPrimeDensityWeightedIntegrability HVRCorrectionBoundaryLimit
open scoped Topology

/-! Spatial Abel convergence from monotone decay of the scalar damping error in L¹. -/
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
  let μ : Measure ℝ := volume.restrict (Set.Ioi 0)
  let F (u : ℝ) : ℂ := ((logPrimeDensity u : ℂ) - 1) * K (x - u)
  let q (n : ℕ) (u : ℝ) : ℝ := Real.exp (-boundaryEps n * u)
  let f (n : ℕ) (u : ℝ) : ℂ := (q n u : ℂ) * F u
  have hF : Integrable F μ := by
    apply (hshift'.norm.const_mul (Real.log 4 + 1)).mono'
      (hden.aestronglyMeasurable.mul hshift'.aestronglyMeasurable)
    filter_upwards [] with u
    have hdenBound : ‖(logPrimeDensity u : ℂ) - 1‖ ≤ Real.log 4 + 1 := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      apply abs_le.mpr
      constructor
      · have hlog : 0 ≤ Real.log 4 := by positivity
        linarith [logPrimeDensity_nonneg u]
      · linarith [logPrimeDensity_le_log_four u]
    simpa only [F, norm_mul] using
      mul_le_mul_of_nonneg_right hdenBound (norm_nonneg (K (x - u)))
  have hpos : ∀ᵐ u : ℝ ∂μ, 0 < u := ae_restrict_mem measurableSet_Ioi
  have hqle (n : ℕ) (u : ℝ) (hu : 0 < u) : q n u ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (boundaryEps_pos n).le) hu.le)
  have hqnonneg (n : ℕ) (u : ℝ) : 0 ≤ q n u := (Real.exp_pos _).le
  have hf (n : ℕ) : Integrable (f n) μ := by
    have hc : Continuous (fun u : ℝ => (q n u : ℂ)) := by dsimp [q]; fun_prop
    apply hF.norm.mono' (hc.aestronglyMeasurable.mul hF.aestronglyMeasurable)
    filter_upwards [hpos] with u hu
    simp only [f, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hqnonneg n u)]
    exact mul_le_of_le_one_left (norm_nonneg _) (hqle n u hu)
  have hnorm (n : ℕ) (u : ℝ) (hu : 0 < u) :
      ‖f n u - F u‖ = (1 - q n u) * ‖F u‖ := by
    have hfac : f n u - F u = ((q n u - 1 : ℝ) : ℂ) * F u := by
      simp only [f, Complex.ofReal_sub, Complex.ofReal_one]
      ring
    rw [hfac, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (sub_nonpos.mpr (hqle n u hu))]
    ring
  have hanti : ∀ᵐ u : ℝ ∂μ, Antitone (fun n : ℕ => ‖f n u - F u‖) := by
    filter_upwards [hpos] with u hu
    intro i j hij
    rw [hnorm j u hu, hnorm i u hu]
    have heps : boundaryEps j ≤ boundaryEps i := by
      unfold boundaryEps
      exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hij 1)
    have hij' : q i u ≤ q j u :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg heps) hu.le)
    exact mul_le_mul_of_nonneg_right (sub_le_sub_left hij' 1) (norm_nonneg _)
  have hlim : ∀ᵐ u : ℝ ∂μ,
      Tendsto (fun n : ℕ => ‖f n u - F u‖) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [hpos] with u hu
    have hc : ContinuousAt (fun a : ℝ => Real.exp (-a * u)) 0 := by fun_prop
    have hq : Tendsto (fun n => q n u) atTop (𝓝 (1 : ℝ)) := by
      simpa only [q, Function.comp_def, neg_zero, zero_mul, Real.exp_zero] using
        hc.tendsto.comp boundaryEps_tendsto
    have h : Tendsto (fun n => (1 - q n u) * ‖F u‖) atTop
        (𝓝 ((1 - 1 : ℝ) * ‖F u‖)) :=
      (tendsto_const_nhds.sub hq).mul tendsto_const_nhds
    simp_rw [fun n => hnorm n u hu]
    simpa only [sub_self, zero_mul] using h
  have hL1 : Tendsto (fun n => ∫ u, ‖f n u - F u‖ ∂μ) atTop (𝓝 (0 : ℝ)) := by
    simpa only [integral_zero] using
      (integral_tendsto_of_tendsto_of_antitone (μ := μ)
        (f := fun n u => ‖f n u - F u‖) (F := fun _ => (0 : ℝ))
        (fun n => ((hf n).sub hF).norm) (by simp) hanti hlim)
  have hmain : Tendsto (fun n => ∫ u, f n u ∂μ) atTop (𝓝 (∫ u, F u ∂μ)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hL1
    rw [← integral_sub (hf n) hF]
    exact norm_integral_le_integral_norm _
  simpa only [μ, f, F, q, dampedError, undamped, Complex.ofReal_exp,
    Complex.ofReal_neg, Complex.ofReal_mul, mul_comm, mul_assoc, mul_left_comm] using hmain

end HVRPrimeDensitySpatialAbel
