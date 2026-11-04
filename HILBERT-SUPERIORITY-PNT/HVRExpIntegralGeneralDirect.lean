import HVRComplexExpIntegralDirect
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! One-variable exponential tails on an arbitrary positive half-line.
The complex improper-integral proof and the real-part bridge adapt the
corresponding Mathlib4 `ImproperIntegrals.lean` arguments by David Loeffler,
Apache 2.0. The integrability input is a direct real majorant. No Lean has
been run locally; external compilation, axiom audit, and swap trace are pending. -/

noncomputable section
open Filter MeasureTheory Real intervalIntegral
open scoped Topology

namespace HVRExpIntegralGeneralDirect

/-- The complex exponential is integrable on any right half-line, by a real
one-variable exponential majorant. -/
theorem complex_exponential_integrable_tail (z : ℂ) (a : ℝ) (hz : 0 < z.re) :
    IntegrableOn (fun u : ℝ => Complex.exp (-z * (u : ℂ))) (Set.Ioi a) volume := by
  have hmajor : IntegrableOn (fun u : ℝ => Real.exp (-z.re * u))
      (Set.Ioi a) volume := exp_neg_integrableOn_Ioi a hz
  have hcont : Continuous (fun u : ℝ => Complex.exp (-z * (u : ℂ))) := by
    fun_prop
  apply Integrable.mono' hmajor hcont.aestronglyMeasurable
  filter_upwards [] with u
  rw [Complex.norm_exp]
  simp [Complex.mul_re]

theorem complex_integrable_exp_mul_Ioi {z : ℂ} (hz : z.re < 0) (a : ℝ) :
    IntegrableOn (fun u : ℝ => Complex.exp (z * (u : ℂ))) (Set.Ioi a) volume := by
  have hp : 0 < (-z).re := by simpa only [Complex.neg_re] using neg_pos.mpr hz
  simpa only [neg_neg] using complex_exponential_integrable_tail (-z) a hp

/-- Tail integral of a complex exponential with negative real exponent. -/
theorem complex_integral_exp_mul_Ioi {z : ℂ} (hz : z.re < 0) (a : ℝ) :
    (∫ u : ℝ in Set.Ioi a, Complex.exp (z * (u : ℂ))) =
      -Complex.exp (z * (a : ℂ)) / z := by
  refine tendsto_nhds_unique
    (intervalIntegral_tendsto_integral_Ioi a
      (complex_integrable_exp_mul_Ioi hz a) tendsto_id) ?_
  simp_rw [integral_exp_mul_complex (c := z) (by aesop), id_eq]
  suffices Tendsto (fun u : ℝ => Complex.exp (z * u)) atTop (𝓝 0) by
    simpa using (this.sub_const (Complex.exp (z * (a : ℂ)))).div_const z
  simpa [Complex.tendsto_exp_nhds_zero_iff] using
    tendsto_const_nhds.neg_mul_atTop hz tendsto_id

/-- Real exponential tail, obtained from the direct complex tail by taking
real parts and without an auxiliary two-variable integral swap. -/
theorem real_integral_exp_mul_Ioi {z : ℝ} (hz : z < 0) (a : ℝ) :
    (∫ u : ℝ in Set.Ioi a, Real.exp (z * u)) = -Real.exp (z * a) / z := by
  simp_rw [Real.exp, ← RCLike.re_to_complex, Complex.ofReal_mul]
  rw [integral_re, complex_integral_exp_mul_Ioi (by simpa using hz),
    RCLike.re_to_complex, RCLike.re_to_complex, Complex.div_ofReal_re, Complex.neg_re]
  exact complex_integrable_exp_mul_Ioi (by simpa using hz) _

end HVRExpIntegralGeneralDirect
