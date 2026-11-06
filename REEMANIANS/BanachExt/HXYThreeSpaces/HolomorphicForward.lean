import RH_HilbertLimit.TwoRoutes.MeasureResolvent
import Mathlib.Analysis.Analytic.Composition

/-!
# Frozen candidate C3: forward construction under the sole hypothesis RH

Actual normalized theta and its exact logarithmic derivative are fixed below.
The witness is constructed from the retained actual Hausdorff measure.
No representing-measure, analyticity, germ-calibration, or sign premise remains.

Prepared for external Lean 4.33.0 compilation. No local Lean execution.
-/

set_option autoImplicit false
noncomputable section

open Filter MeasureTheory ComplexConjugate
open scoped Topology

namespace HXYThreeSpaces

open RH_HilbertLimit RH_HilbertLimit.TwoRoutes

/-- The literal complex plane with the real ray `(-infinity,-1]` removed. -/
def Omega : Set ℂ := {z : ℂ | -1 < z.re ∨ z.im ≠ 0}

/-- Actual theta, normalized to have value and derivative one at the origin. -/
def normalizedXi (z : ℂ) : ℂ :=
  AWPIRH.theta (z / (actualKappa : ℂ)) / AWPIRH.theta 0

/-- The fixed actual normalized logarithmic derivative, initially a germ at zero. -/
def normalizedLogDerivative (z : ℂ) : ℂ :=
  actualLogDerivative (z / (actualKappa : ℂ)) / (actualKappa : ℂ)

/-- Frozen candidate C3. Every witness extends the same fixed actual germ. -/
def HolExt : Prop :=
  ∃ G : ℂ → ℂ,
    AnalyticOnNhd ℂ G Omega ∧
      normalizedLogDerivative =ᶠ[𝓝 (0 : ℂ)] G

/-- The denominator-free presentation of exactly the same candidate. -/
def HolODE : Prop :=
  ∃ G : ℂ → ℂ,
    AnalyticOnNhd ℂ G Omega ∧
      ∀ z ∈ Omega, deriv normalizedXi z = G z * normalizedXi z

theorem actualKappa_complex_ne_zero : (actualKappa : ℂ) ≠ 0 := by
  exact_mod_cast ne_of_gt actualKappa_pos

theorem zero_mem_Omega : (0 : ℂ) ∈ Omega := by
  left
  norm_num

theorem isOpen_Omega : IsOpen Omega := by
  have hre : IsOpen {z : ℂ | -1 < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have him : IsOpen {z : ℂ | z.im ≠ 0} :=
    (isClosed_singleton : IsClosed ({0} : Set ℝ)).isOpen_compl.preimage
      Complex.continuous_im
  exact hre.union him

theorem normalizedXi_entire : AnalyticOnNhd ℂ normalizedXi Set.univ := by
  intro z _
  have hscale : AnalyticAt ℂ (fun w : ℂ => w / (actualKappa : ℂ)) z :=
    analyticAt_id.div analyticAt_const actualKappa_complex_ne_zero
  have htheta : AnalyticAt ℂ
      (fun w : ℂ => AWPIRH.theta (w / (actualKappa : ℂ))) z :=
    AnalyticAt.comp (g := AWPIRH.theta)
      (f := fun w : ℂ => w / (actualKappa : ℂ)) (x := z)
      (AWPIRH.theta_analyticAt (z / (actualKappa : ℂ))) hscale
  exact htheta.div
    analyticAt_const AngularMaster.actual_theta_zero_ne_zero

@[simp] theorem normalizedXi_zero : normalizedXi 0 = 1 := by
  simp [normalizedXi, AngularMaster.actual_theta_zero_ne_zero]

theorem normalizedXi_zero_ne_zero : normalizedXi 0 ≠ 0 := by
  rw [normalizedXi_zero]
  exact one_ne_zero

theorem deriv_normalizedXi (z : ℂ) :
    deriv normalizedXi z =
      (deriv AWPIRH.theta (z / (actualKappa : ℂ)) *
        (1 / (actualKappa : ℂ))) / AWPIRH.theta 0 := by
  have htheta :=
    (AWPIRH.theta_analyticAt (z / (actualKappa : ℂ))).differentiableAt.hasDerivAt
  have hscale := (hasDerivAt_id z).div_const (actualKappa : ℂ)
  have h := (htheta.comp z hscale).div_const (AWPIRH.theta 0)
  exact h.deriv

/-- Exact semantic binding: this germ is the logarithmic derivative of F. -/
theorem normalizedLogDerivative_eq_logDerivative (z : ℂ) :
    normalizedLogDerivative z = deriv normalizedXi z / normalizedXi z := by
  rw [deriv_normalizedXi]
  unfold normalizedLogDerivative actualLogDerivative normalizedXi
  by_cases hz : AWPIRH.theta (z / (actualKappa : ℂ)) = 0
  · simp [hz]
  · field_simp [actualKappa_complex_ne_zero,
      AngularMaster.actual_theta_zero_ne_zero, hz]
    <;> ring

theorem eventually_normalizedXi_ne_zero :
    ∀ᶠ z : ℂ in 𝓝 (0 : ℂ), normalizedXi z ≠ 0 := by
  have hcontinuous : Continuous normalizedXi :=
    continuous_iff_continuousAt.mpr
      (fun z => (normalizedXi_entire z (Set.mem_univ z)).continuousAt)
  exact ((isClosed_singleton : IsClosed ({0} : Set ℂ)).isOpen_compl.preimage
    hcontinuous).mem_nhds normalizedXi_zero_ne_zero

/-- The literal cut plane is contained in the normalized kernel denominator domain. -/
theorem Omega_subset_resolvent_domain_one :
    Omega ⊆ MeasureResolvent.domain 1 := by
  intro z hz q hzero
  by_cases hq : (q : ℝ) = 0
  · simpa [MeasureResolvent.denominator, hq] using hzero
  · have hqpos : 0 < (q : ℝ) := lt_of_le_of_ne q.property.1 (Ne.symm hq)
    have him := congrArg Complex.im hzero
    have hre := congrArg Complex.re hzero
    have himmul : z.im * (q : ℝ) = 0 := by
      simpa only [MeasureResolvent.denominator, Complex.ofReal_one, one_mul,
        Complex.add_im, Complex.one_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, zero_add, Complex.zero_im] using him
    have hzim : z.im = 0 := (mul_eq_zero.mp himmul).resolve_right hq
    rcases hz with hzr | hzi
    · have hreal : 1 + z.re * (q : ℝ) = 0 := by
        simpa only [MeasureResolvent.denominator, Complex.ofReal_one, one_mul,
          Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, mul_zero, sub_zero, Complex.zero_re] using hre
      have hmul : (-1 : ℝ) * (q : ℝ) < z.re * (q : ℝ) :=
        mul_lt_mul_of_pos_right hzr hqpos
      have hqone := q.property.2
      nlinarith
    · exact hzi hzim

theorem scaled_resolvent_eq_transform_one
    (σ : Measure MeasureResolvent.UnitInterval) (z : ℂ) :
    MeasureResolvent.resolvent actualKappa σ (z / (actualKappa : ℂ)) /
        (actualKappa : ℂ) = MeasureResolvent.transform 1 σ 0 z := by
  have hden : ∀ q : MeasureResolvent.UnitInterval,
      MeasureResolvent.denominator actualKappa (z / (actualKappa : ℂ)) q =
        MeasureResolvent.denominator 1 z q := by
    intro q
    simp only [MeasureResolvent.denominator, Complex.ofReal_one,
      mul_div_cancel₀ z actualKappa_complex_ne_zero, one_mul]
  have htransform :
      MeasureResolvent.transform actualKappa σ 0 (z / (actualKappa : ℂ)) =
        MeasureResolvent.transform 1 σ 0 z := by
    unfold MeasureResolvent.transform
    apply integral_congr_ae
    filter_upwards [] with q
    simp only [MeasureResolvent.kernel, hden q]
  unfold MeasureResolvent.resolvent
  rw [htransform]
  exact (div_eq_iff actualKappa_complex_ne_zero).mpr (mul_comm _ _)

/-- The existing all-order actual moment calibration gives the normalized germ. -/
theorem normalizedLogDerivative_transform_germ
    (σ : Measure MeasureResolvent.UnitInterval) [IsFiniteMeasure σ]
    (hmoment : ∀ n : ℕ,
      (∫ q, (q : ℝ) ^ n ∂σ) = actualNormalizedMoment n) :
    normalizedLogDerivative =ᶠ[𝓝 (0 : ℂ)] MeasureResolvent.transform 1 σ 0 := by
  have hscale : Tendsto (fun z : ℂ => z / (actualKappa : ℂ))
      (𝓝 (0 : ℂ)) (𝓝 (0 : ℂ)) := by
    have hc : Continuous (fun z : ℂ => z / (actualKappa : ℂ)) := by fun_prop
    simpa only [zero_div] using hc.tendsto (0 : ℂ)
  have hscaled := (actual_logDerivative_resolvent_germ σ hmoment).comp_tendsto hscale
  filter_upwards [hscaled] with z hz
  change actualLogDerivative (z / (actualKappa : ℂ)) =
    MeasureResolvent.resolvent actualKappa σ (z / (actualKappa : ℂ)) at hz
  change actualLogDerivative (z / (actualKappa : ℂ)) / (actualKappa : ℂ) = _
  rw [hz, scaled_resolvent_eq_transform_one]

theorem holExt_of_actual_moments
    (σ : Measure MeasureResolvent.UnitInterval) [IsFiniteMeasure σ]
    (hmoment : ∀ n : ℕ,
      (∫ q, (q : ℝ) ^ n ∂σ) = actualNormalizedMoment n) : HolExt := by
  refine ⟨MeasureResolvent.transform 1 σ 0, ?_,
    normalizedLogDerivative_transform_germ σ hmoment⟩
  intro z hz
  exact MeasureResolvent.analyticAt_transform (by norm_num : (0 : ℝ) < 1)
    (Omega_subset_resolvent_domain_one hz) 0

/-- The H00 construction produces C3 with no supplied measure or germ witness. -/
theorem holExt_of_H00 (h : H00) : HolExt :=
  holExt_of_actual_moments (actualHausdorffMeasure h) (actualHausdorffMeasure_moment h)

/-- C3 forward endpoint. RH is the sole hypothesis. -/
theorem holExt_of_nativeRH (hRH : _root_.RiemannHypothesis) : HolExt :=
  holExt_of_H00 (H00_of_nativeRH hRH)

end HXYThreeSpaces
