import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic

/-!
One-dimensional integration-by-parts step for constructing a physical
Fourier wave directly from a compact seed. This candidate is generic in the
oscillatory phase: it assumes a differentiable unit-bounded phase with a
constant scalar logarithmic derivative. All integrability hypotheses are
explicit. It makes no use of the Schwartz Fourier transform as an object.

No Lean was executed locally. External compile, axiom audit and a transitive
dependency trace against the targeted two-dimensional swap remain necessary.
-/

noncomputable section
open Filter MeasureTheory

namespace HVROneDimensionalDecay

/-- Integration by parts converts a phase factor into the derivative of the
seed using only an improper one-dimensional integral. -/
theorem phase_integral_mul_eq_neg_derivative_integral
    (f f' g : ℝ → ℂ) (λ : ℂ)
    (hf : ∀ t : ℝ, HasDerivAt f (f' t) t)
    (hg : ∀ t : ℝ, HasDerivAt g (λ * g t) t)
    (hfg : Integrable (fun t : ℝ => f t * g t))
    (hf'g : Integrable (fun t : ℝ => f' t * g t)) :
    λ * (∫ t : ℝ, f t * g t) = -(∫ t : ℝ, f' t * g t) := by
  have hfg' : Integrable (fun t : ℝ => f t * (λ * g t)) := by
    have h := hfg.const_mul λ
    convert h using 1
    funext t
    ring
  have hibp := MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := f) (u' := f') (v := g) (v' := fun t : ℝ => λ * g t)
    (fun t _ => hf t) (fun t _ => hg t) hfg' hf'g hfg
  have hscalar : (∫ t : ℝ, f t * (λ * g t)) =
      λ * (∫ t : ℝ, f t * g t) := by
    simp_rw [show ∀ t : ℝ, f t * (λ * g t) = λ * (f t * g t) by
      intro t
      ring]
    exact integral_const_mul λ _
  rw [hscalar] at hibp
  exact hibp

/-- The phase-integral norm has the first-derivative decay bound. -/
theorem phase_integral_derivative_bound
    (f f' g : ℝ → ℂ) (λ : ℂ)
    (hf : ∀ t : ℝ, HasDerivAt f (f' t) t)
    (hg : ∀ t : ℝ, HasDerivAt g (λ * g t) t)
    (hfg : Integrable (fun t : ℝ => f t * g t))
    (hf'g : Integrable (fun t : ℝ => f' t * g t))
    (hf' : Integrable f') (hgnorm : ∀ t : ℝ, ‖g t‖ ≤ 1) :
    ‖λ‖ * ‖∫ t : ℝ, f t * g t‖ ≤ ∫ t : ℝ, ‖f' t‖ := by
  have hbound : ‖∫ t : ℝ, f' t * g t‖ ≤ ∫ t : ℝ, ‖f' t‖ := by
    apply norm_integral_le_of_norm_le hf'.norm
    filter_upwards [] with t
    calc
      ‖f' t * g t‖ = ‖f' t‖ * ‖g t‖ := norm_mul _ _
      _ ≤ ‖f' t‖ * 1 := mul_le_mul_of_nonneg_left (hgnorm t) (norm_nonneg _)
      _ = ‖f' t‖ := mul_one _
  calc
    ‖λ‖ * ‖∫ t : ℝ, f t * g t‖ = ‖λ * (∫ t : ℝ, f t * g t)‖ :=
      (norm_mul _ _).symm
    _ = ‖∫ t : ℝ, f' t * g t‖ := by
      rw [phase_integral_mul_eq_neg_derivative_integral f f' g λ hf hg hfg hf'g,
        norm_neg]
    _ ≤ ∫ t : ℝ, ‖f' t‖ := hbound

end HVROneDimensionalDecay
