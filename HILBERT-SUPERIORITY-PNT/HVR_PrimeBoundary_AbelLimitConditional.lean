import HVR_PrimeDensity_BoundaryLimit
import HVR_PrimeBoundary_OrdinaryFrequencyDecay
import Mathlib.MeasureTheory.Integral.Bochner.Basic

noncomputable section
open Filter MeasureTheory ENNReal
open scoped Topology ENNReal
open HVRCorrectionBoundaryLimit HVRPrimeDensityLaplace
open HVRPrimeDensityBoundaryLimit HVRPrimeBoundaryOrdinaryFrequencyDecay
open HVRSmoothingBoundaryExtension

/-! A candidate Abel-to-boundary frequency integral limit along the audited
positive reciprocal sequence. Pointwise convergence is discharged using the
actual prime-density Laplace boundary theorem. Measurability and an explicit
integrable majorant remain hypotheses. This is not yet an undamped convolution
identity or a proof of PNT. No Lean was run locally. -/
namespace HVRPrimeBoundaryAbelLimitConditional

def frequencyIntegrand (ψ : ℝ → ℂ) (x a t : ℝ) : ℂ :=
  (ψ t * Complex.exp ((t : ℂ) * Complex.I * (x : ℂ))) *
    primeDensityLaplace ((a : ℂ) + (t : ℂ) * Complex.I)

/-- Reverse Fatou controls the upper limit of a nonnegative L¹ error.
The measurable representatives agree simultaneously off a single null set. -/
theorem lintegral_error_zero_of_reverse_fatou
    (e : ℕ → ℝ → ℝ≥0∞) (b : ℝ → ℝ≥0∞)
    (hm : ∀ n, AEMeasurable (e n) volume)
    (hb : ∀ n, e n ≤ᵐ[volume] b)
    (hfin : (∫⁻ t : ℝ, b t) ≠ ∞)
    (hz : ∀ᵐ t : ℝ ∂volume, Tendsto (fun n => e n t) atTop (𝓝 0)) :
    Tendsto (fun n => ∫⁻ t : ℝ, e n t) atTop (𝓝 0) := by
  let E (n : ℕ) := (hm n).mk (e n)
  have heq (n : ℕ) : e n =ᵐ[volume] E n := (hm n).ae_eq_mk
  have hball (n : ℕ) : E n ≤ᵐ[volume] b := by
    filter_upwards [heq n, hb n] with t ht h
    rw [← ht]
    exact h
  have hall : ∀ᵐ t : ℝ ∂volume, ∀ n, e n t = E n t := ae_all_iff.mpr heq
  have hz' : ∀ᵐ t : ℝ ∂volume, Tendsto (fun n => E n t) atTop (𝓝 0) := by
    filter_upwards [hall, hz] with t hte htz
    exact htz.congr' (Filter.Eventually.of_forall hte)
  have hu : limsup (fun n => ∫⁻ t : ℝ, E n t) atTop ≤ 0 := calc
    _ ≤ ∫⁻ t : ℝ, limsup (fun n => E n t) atTop :=
      limsup_lintegral_le b (fun n => (hm n).measurable_mk) hball hfin
    _ = ∫⁻ _ : ℝ, (0 : ℝ≥0∞) := lintegral_congr_ae (hz'.mono fun _ h => h.limsup_eq)
    _ = 0 := by simp
  have hE : Tendsto (fun n => ∫⁻ t : ℝ, E n t) atTop (𝓝 0) :=
    tendsto_of_le_liminf_of_limsup_le bot_le hu
  exact hE.congr' (Filter.Eventually.of_forall fun n => (lintegral_congr_ae (heq n)).symm)

/-- Convert a pointwise complex limit into an integral limit using the
triangle inequality, a scalar reverse-Fatou bound and L¹ continuity. -/
theorem integral_tendsto_of_fatou_error
    (F : ℕ → ℝ → ℂ) (f : ℝ → ℂ) (w : ℝ → ℝ)
    (hm : ∀ n, AEStronglyMeasurable (F n) volume) (hw : Integrable w volume)
    (hb : ∀ n, ∀ᵐ t : ℝ ∂volume, ‖F n t‖ ≤ w t)
    (hz : ∀ᵐ t : ℝ ∂volume, Tendsto (fun n => F n t) atTop (𝓝 (f t))) :
    Tendsto (fun n => ∫ t : ℝ, F n t) atTop (𝓝 (∫ t : ℝ, f t)) := by
  have hm' : AEStronglyMeasurable f volume := aestronglyMeasurable_of_tendsto_ae _ hm hz
  refine tendsto_integral_of_L1 f hm'
    (Filter.Eventually.of_forall fun n => hw.mono' (hm n) (hb n)) ?_
  let e (n : ℕ) (t : ℝ) := ENNReal.ofReal ‖F n t - f t‖
  let b (t : ℝ) := ENNReal.ofReal (w t + w t)
  have hfb : ∀ᵐ t : ℝ ∂volume, ‖f t‖ ≤ w t := by
    have hba : ∀ᵐ t : ℝ ∂volume, ∀ n, ‖F n t‖ ≤ w t := ae_all_iff.mpr hb
    filter_upwards [hba, hz] with t ht h
    exact le_of_tendsto' h.norm ht
  have he : ∀ n, AEMeasurable (e n) volume := fun n =>
    ENNReal.measurable_ofReal.comp_aemeasurable ((hm n).sub hm').norm.aemeasurable
  have heb (n : ℕ) : e n ≤ᵐ[volume] b := by
    filter_upwards [hb n, hfb] with t h₁ h₂
    exact ENNReal.ofReal_le_ofReal ((norm_sub_le _ _).trans (add_le_add h₁ h₂))
  have hpos : ∀ᵐ t : ℝ ∂volume, 0 ≤ w t + w t := by
    filter_upwards [hb 0] with t ht
    exact add_nonneg ((norm_nonneg _).trans ht) ((norm_nonneg _).trans ht)
  have hfin : (∫⁻ t : ℝ, b t) ≠ ∞ :=
    ((hasFiniteIntegral_iff_ofReal hpos).mp (hw.add hw).hasFiniteIntegral).ne
  have helim : ∀ᵐ t : ℝ ∂volume, Tendsto (fun n => e n t) atTop (𝓝 0) := by
    filter_upwards [hz] with t ht
    have ht' := tendsto_iff_norm_sub_tendsto_zero.mp ht
    simpa only [e, Function.comp_def, ENNReal.ofReal_zero] using
      ((ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp ht')
  simpa only [e, ofReal_norm] using
    lintegral_error_zero_of_reverse_fatou e b he heb hfin helim

/-- Conditional frequency-side Abel limit. The explicit uniform domination and
measurability assumptions are not discharged by this lemma. -/
theorem frequency_integral_tendsto_boundary_of_dominated
    (ψ : ℝ → ℂ) (x C : ℝ) (hψ : Integrable ψ volume)
    (hmeas : ∀ n : ℕ, AEStronglyMeasurable
      (frequencyIntegrand ψ x (boundaryEps n)) volume)
    (hdom : ∀ n : ℕ, ∀ᵐ t : ℝ ∂volume,
      ‖frequencyIntegrand ψ x (boundaryEps n) t‖ ≤ C * ‖ψ t‖) :
    Tendsto (fun n : ℕ => ∫ t : ℝ, frequencyIntegrand ψ x (boundaryEps n) t)
      atTop (𝓝 (ordinaryBoundary ψ x)) := by
  have hmajor : Integrable (fun t : ℝ => C * ‖ψ t‖) volume :=
    hψ.norm.const_mul C
  have hlim : ∀ᵐ t : ℝ ∂volume,
      Tendsto (fun n : ℕ => frequencyIntegrand ψ x (boundaryEps n) t)
        atTop (𝓝 ((ψ t * Complex.exp ((t : ℂ) * Complex.I * (x : ℂ))) *
          patchedShift ((t : ℂ) * Complex.I))) := by
    filter_upwards [] with t
    have hcst : Tendsto (fun _ : ℕ =>
        ψ t * Complex.exp ((t : ℂ) * Complex.I * (x : ℂ))) atTop
        (𝓝 (ψ t * Complex.exp ((t : ℂ) * Complex.I * (x : ℂ)))) :=
      tendsto_const_nhds
    have h := hcst.mul (primeDensityLaplace_boundaryEps_tendsto t)
    simpa only [frequencyIntegrand] using h
  exact integral_tendsto_of_fatou_error _ _ _ hmeas hmajor hdom hlim

end HVRPrimeBoundaryAbelLimitConditional
