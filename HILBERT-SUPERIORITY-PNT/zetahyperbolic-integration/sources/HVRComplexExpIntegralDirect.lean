import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.Tactic

/-!
One-variable candidate for the positive-half-line complex Laplace transform.
The elementary real exponential majorant uses `exp_neg_integrableOn_Ioi`.
The improper-integral argument below adapts the proof of
`integral_exp_mul_complex_Ioi` in Mathlib4,
Mathlib/Analysis/SpecialFunctions/ImproperIntegrals.lean,
copyright (c) 2023 David Loeffler, Apache 2.0.

No local Lean execution, external kernel audit, or dependency trace has been
performed for this candidate. Even if validated, Mathlib foundations remain.
-/

noncomputable section
open Filter MeasureTheory Real intervalIntegral
open scoped Topology

namespace HVRComplexExpIntegralDirect

theorem exponential_integrable_direct (z : ℂ) (hz : 0 < z.re) :
    IntegrableOn (fun u : ℝ => Complex.exp (-z * (u : ℂ))) (Set.Ioi 0) volume := by
  have hmajor : IntegrableOn (fun u : ℝ => Real.exp (-z.re * u))
      (Set.Ioi 0) volume := exp_neg_integrableOn_Ioi 0 hz
  have hcont : Continuous (fun u : ℝ => Complex.exp (-z * (u : ℂ))) := by
    fun_prop
  apply Integrable.mono' hmajor hcont.aestronglyMeasurable
  filter_upwards [] with u
  rw [Complex.norm_exp]
  simp [Complex.mul_re]

theorem exponential_integral_eq_inv_direct (z : ℂ) (hz : 0 < z.re) :
    (∫ u : ℝ in Set.Ioi 0, Complex.exp (-z * (u : ℂ))) = z⁻¹ := by
  have hzneg : (-z).re < 0 := by
    rw [Complex.neg_re]
    linarith
  have h : (∫ u : ℝ in Set.Ioi 0, Complex.exp ((-z) * (u : ℂ))) =
      -Complex.exp ((-z) * (0 : ℂ)) / (-z) := by
    refine tendsto_nhds_unique
      (intervalIntegral_tendsto_integral_Ioi 0
        (exponential_integrable_direct z hz) tendsto_id) ?_
    simp_rw [integral_exp_mul_complex (c := -z) (by aesop), id_eq]
    suffices Tendsto (fun x : ℝ => Complex.exp ((-z) * x)) atTop (𝓝 0) by
      simpa using this.sub_const _ |>.div_const _
    simpa [Complex.tendsto_exp_nhds_zero_iff] using
      tendsto_const_nhds.neg_mul_atTop hzneg tendsto_id
  simpa using h

end HVRComplexExpIntegralDirect
