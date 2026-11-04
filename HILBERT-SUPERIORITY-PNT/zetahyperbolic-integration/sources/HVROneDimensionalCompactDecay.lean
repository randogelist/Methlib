import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-! Compact-interval one-variable integration-by-parts candidate. Unlike the
global improper-integral integration-by-parts lemma, this proof restricts the
integrals to a supplied finite interval on which the seed and derivative
have zero boundary/off-interval values. The phase is abstract, has a constant
scalar derivative factor, and is bounded in norm. No Lean was run locally;
an external compile, named axiom audit and target-swap trace are required. -/

noncomputable section
open Filter MeasureTheory

namespace HVROneDimensionalCompactDecay

/-- Finite-interval integration by parts, followed by restriction to the
whole line using the explicit support assumptions. -/
theorem phase_integral_mul_eq_neg_derivative_integral
    (a b : ℝ) (hab : a ≤ b) (f f' g : ℝ → ℂ) (c : ℂ)
    (hf : ∀ t : ℝ, HasDerivAt f (f' t) t)
    (hg : ∀ t : ℝ, HasDerivAt g (c * g t) t)
    (hf'cont : Continuous f') (hgcont : Continuous g)
    (ha : f a = 0) (hb : f b = 0)
    (hfsupport : ∀ t : ℝ, t ∉ Set.Ioc a b → f t = 0)
    (hf'support : ∀ t : ℝ, t ∉ Set.Ioc a b → f' t = 0) :
    c * (∫ t : ℝ, f t * g t) = -(∫ t : ℝ, f' t * g t) := by
  have hcontg' : Continuous (fun t : ℝ => c * g t) :=
    continuous_const.mul hgcont
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := a) (b := b) (u := f) (u' := f') (v := g)
    (v' := fun t : ℝ => c * g t)
    (fun t _ => hf t) (fun t _ => hg t)
    (hf'cont.intervalIntegrable a b) (hcontg'.intervalIntegrable a b)
  simp only [ha, hb, zero_mul, sub_zero, zero_sub] at hibp
  have hscalar : (∫ t in a..b, f t * (c * g t)) =
      c * (∫ t in a..b, f t * g t) := by
    simp_rw [show ∀ t : ℝ, f t * (c * g t) = c * (f t * g t) by
      intro t
      ring]
    exact intervalIntegral.integral_const_mul c _
  rw [hscalar] at hibp
  have hf_full : (∫ t in a..b, f t * g t) = ∫ t : ℝ, f t * g t := by
    rw [intervalIntegral.integral_of_le hab]
    apply setIntegral_eq_integral_of_ae_compl_eq_zero
    filter_upwards [] with t ht
    rw [hfsupport t ht, zero_mul]
  have hf'_full : (∫ t in a..b, f' t * g t) = ∫ t : ℝ, f' t * g t := by
    rw [intervalIntegral.integral_of_le hab]
    apply setIntegral_eq_integral_of_ae_compl_eq_zero
    filter_upwards [] with t ht
    rw [hf'support t ht, zero_mul]
  rw [hf_full, hf'_full] at hibp
  exact hibp

/-- The corresponding norm estimate. -/
theorem phase_integral_derivative_bound
    (a b : ℝ) (hab : a ≤ b) (f f' g : ℝ → ℂ) (c : ℂ)
    (hf : ∀ t : ℝ, HasDerivAt f (f' t) t)
    (hg : ∀ t : ℝ, HasDerivAt g (c * g t) t)
    (hf'cont : Continuous f') (hgcont : Continuous g)
    (ha : f a = 0) (hb : f b = 0)
    (hfsupport : ∀ t : ℝ, t ∉ Set.Ioc a b → f t = 0)
    (hf'support : ∀ t : ℝ, t ∉ Set.Ioc a b → f' t = 0)
    (hf' : Integrable f') (hgnorm : ∀ t : ℝ, ‖g t‖ ≤ 1) :
    ‖c‖ * ‖∫ t : ℝ, f t * g t‖ ≤ ∫ t : ℝ, ‖f' t‖ := by
  have hbound : ‖∫ t : ℝ, f' t * g t‖ ≤ ∫ t : ℝ, ‖f' t‖ := by
    apply norm_integral_le_of_norm_le hf'.norm
    filter_upwards [] with t
    calc
      ‖f' t * g t‖ = ‖f' t‖ * ‖g t‖ := norm_mul _ _
      _ ≤ ‖f' t‖ * 1 := mul_le_mul_of_nonneg_left (hgnorm t) (norm_nonneg _)
      _ = ‖f' t‖ := mul_one _
  calc
    ‖c‖ * ‖∫ t : ℝ, f t * g t‖ = ‖c * (∫ t : ℝ, f t * g t)‖ :=
      (norm_mul _ _).symm
    _ = ‖∫ t : ℝ, f' t * g t‖ := by
      rw [phase_integral_mul_eq_neg_derivative_integral a b hab f f' g c
        hf hg hf'cont hgcont ha hb hfsupport hf'support, norm_neg]
    _ ≤ ∫ t : ℝ, ‖f' t‖ := hbound

end HVROneDimensionalCompactDecay
