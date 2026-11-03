import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

/-!
Candidate independent proof of the real exponential mode integral needed by
PrimeSpectralResolvent. It uses a general improper fundamental theorem of
calculus for a nonnegative derivative, plus elementary exponential calculus.
No specialized exponential improper-integral formula is used in the proof.

This candidate has not been externally compiled or audited. A successful
compilation and theorem-level audit, followed by a recursive dependency check,
are required before claiming verified independence from an existing endpoint.
-/

noncomputable section
open Real Set Filter MeasureTheory
open scoped Topology

namespace NativeExpIntegral

/-- Primitive of an exponential with nonzero exponent coefficient. -/
theorem exp_primitive_derivative (c : ℝ) (hc : c ≠ 0) (x : ℝ) :
    HasDerivAt (fun t : ℝ => Real.exp (c * t) / c)
      (Real.exp (c * x)) x := by
  conv => congr
  rw [← mul_div_cancel_right₀ (Real.exp (c * x)) hc]
  apply ((Real.hasDerivAt_exp _).comp x _).div_const c
  simpa only [mul_one] using! ((hasDerivAt_id x).const_mul c)

/-- The primitive tends to zero for a strictly negative coefficient. -/
theorem exp_primitive_tendsto_zero (c : ℝ) (hc : c < 0) :
    Tendsto (fun t : ℝ => Real.exp (c * t) / c) atTop (𝓝 0) := by
  have harg : Tendsto (fun t : ℝ => c * t) atTop atBot :=
    tendsto_const_nhds.neg_mul_atTop hc tendsto_id
  have hexp : Tendsto (fun t : ℝ => Real.exp (c * t)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp harg
  simpa only [zero_div] using hexp.div_const c

/-- The nonnegative exponential derivative is integrable on the half-line. -/
theorem exp_negative_integrable (c b : ℝ) (hc : c < 0) :
    IntegrableOn (fun t : ℝ => Real.exp (c * t)) (Set.Ioi b) volume := by
  apply integrableOn_Ioi_deriv_of_nonneg'
    (g := fun t : ℝ => Real.exp (c * t) / c)
  · intro x hx
    exact exp_primitive_derivative c (ne_of_lt hc) x
  · intro x hx
    exact le_of_lt (Real.exp_pos _)
  · exact exp_primitive_tendsto_zero c hc

/-- Exact half-line integral for a negative real coefficient. -/
theorem exp_negative_integral (c b : ℝ) (hc : c < 0) :
    (∫ t : ℝ in Set.Ioi b, Real.exp (c * t)) =
      -Real.exp (c * b) / c := by
  have h := integral_Ioi_of_hasDerivAt_of_nonneg'
    (g := fun t : ℝ => Real.exp (c * t) / c)
    (g' := fun t : ℝ => Real.exp (c * t))
    (a := b) (l := 0)
    (fun x hx => exp_primitive_derivative c (ne_of_lt hc) x)
    (fun x hx => le_of_lt (Real.exp_pos _))
    (exp_primitive_tendsto_zero c hc)
  simpa only [zero_sub, neg_div] using h

/-- Project-shaped statement: one nonnegative-energy spectral mode is
integrable for positive shifted energy, for any real scalar weight. -/
theorem mode_integrable (a e w : ℝ) (h : 0 < w + e) :
    IntegrableOn (fun t : ℝ => a * Real.exp (-(w + e) * t))
      (Set.Ioi 0) volume := by
  exact (exp_negative_integrable (-(w + e)) 0 (by linarith)).const_mul a

/-- Project-shaped half-line mode integral, with the same hypotheses and
conclusion as the existing spectral resolvent component. -/
theorem mode_integral (a e w : ℝ) (h : 0 < w + e) :
    (∫ t : ℝ in Set.Ioi 0, a * Real.exp (-(w + e) * t)) = a / (w + e) := by
  have he : (∫ t : ℝ in Set.Ioi 0, Real.exp (-(w + e) * t)) =
      (w + e)⁻¹ := by
    simpa only [mul_zero, Real.exp_zero, neg_div_neg_eq, one_div] using
      exp_negative_integral (-(w + e)) 0 (by linarith)
  rw [integral_const_mul, he, div_eq_mul_inv]

end NativeExpIntegral
