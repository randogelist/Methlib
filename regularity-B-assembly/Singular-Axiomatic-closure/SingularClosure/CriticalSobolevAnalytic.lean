import SingularClosure.PhysicalEnstrophy
import Mathlib.Analysis.Complex.Hadamard
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Analytic tools for the critical Fourier Sobolev estimate

These are actual differentiation and three-lines lemmas.  No Sobolev
embedding, operator interpolation result, or endpoint bound is assumed.
-/

set_option autoImplicit false
set_option Elab.async true

open Set Filter MeasureTheory Metric
open scoped Topology

namespace SingularClosure

noncomputable section

/-- Jointly continuous integrands and derivatives may be differentiated under
the actual finite cube integral. -/
theorem critical_hasDerivAt_cube_integral
    (F D : ℂ → Vec → ℂ)
    (hF : Continuous (fun q : ℂ × Vec => F q.1 q.2))
    (hD : Continuous (fun q : ℂ × Vec => D q.1 q.2))
    (hd : ∀ z x, HasDerivAt (fun w => F w x) (D z x) z) (z : ℂ) :
    HasDerivAt (fun w => ∫ x in unitCube, F w x)
      (∫ x in unitCube, D z x) z := by
  have hFc (w : ℂ) : Continuous (F w) :=
    hF.comp (continuous_const.prodMk continuous_id)
  have hDc (w : ℂ) : Continuous (D w) :=
    hD.comp (continuous_const.prodMk continuous_id)
  obtain ⟨C, hC⟩ := ((isCompact_closedBall z 1).prod isCompact_unitCube).
    exists_bound_of_continuousOn hD.continuousOn
  have hbound : ∀ᵐ x ∂volume.restrict unitCube,
      ∀ w ∈ closedBall z 1, ‖D w x‖ ≤ C := by
    filter_upwards [ae_restrict_mem isCompact_unitCube.measurableSet] with x hx
    intro w hw
    exact hC (w, x) ⟨hw, hx⟩
  have hdiff : ∀ᵐ x ∂volume.restrict unitCube,
      ∀ w ∈ closedBall z 1, HasDerivAt (fun v => F v x) (D w x) w :=
    Filter.Eventually.of_forall (fun x w _ => hd w x)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict unitCube) (F := F) (F' := D)
    (bound := fun _ : Vec => C)
    (closedBall_mem_nhds z (by norm_num : (0 : ℝ) < 1))
    (Filter.Eventually.of_forall (fun w => (hFc w).aestronglyMeasurable))
    ((hFc z).continuousOn.integrableOn_compact isCompact_unitCube)
    (hDc z).aestronglyMeasurable hbound
    (continuous_const.continuousOn.integrableOn_compact isCompact_unitCube)
    hdiff).2

theorem critical_differentiable_cube_integral
    (F D : ℂ → Vec → ℂ)
    (hF : Continuous (fun q : ℂ × Vec => F q.1 q.2))
    (hD : Continuous (fun q : ℂ × Vec => D q.1 q.2))
    (hd : ∀ z x, HasDerivAt (fun w => F w x) (D z x) z) :
    Differentiable ℂ (fun w => ∫ x in unitCube, F w x) :=
  fun z => (critical_hasDerivAt_cube_integral F D hF hD hd z).differentiableAt

/-- The midpoint version of the proved Hadamard theorem, with explicit
boundedness on the full closed strip. -/
theorem critical_three_lines_midpoint (F : ℂ → ℂ)
    (hF : Differentiable ℂ F)
    (hbounded : ∃ C : ℝ, ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 → ‖F z‖ ≤ C)
    (A B : ℝ)
    (hleft : ∀ z : ℂ, z.re = 0 → ‖F z‖ ≤ A)
    (hright : ∀ z : ℂ, z.re = 1 → ‖F z‖ ≤ B) :
    ‖F (1 / 2 : ℂ)‖ ≤ Real.sqrt A * Real.sqrt B := by
  obtain ⟨C, hC⟩ := hbounded
  have hB : BddAbove ((norm ∘ F) ''
      Complex.HadamardThreeLines.verticalClosedStrip 0 1) := by
    refine ⟨C, ?_⟩
    rintro y ⟨z, hz, rfl⟩
    exact hC z hz.1 hz.2
  have h := Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip₀₁'
    F (z := (1 / 2 : ℂ)) (a := A) (b := B)
    (by norm_num [Complex.HadamardThreeLines.verticalClosedStrip])
    hF.diffContOnCl hB
    (fun z hz => hleft z hz) (fun z hz => hright z hz)
  simpa only [Complex.div_ofNat_re, Complex.one_re, Real.sqrt_eq_rpow,
    show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] using h

/-- A positive real spectral weight raised to a complex exponent, written
using the entire exponential in the exponent variable. -/
def criticalComplexWeight (w : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (z * (Real.log w : ℂ))

theorem criticalComplexWeight_norm {w : ℝ} (hw : 0 < w) (z : ℂ) :
    ‖criticalComplexWeight w z‖ = w ^ z.re := by
  rw [criticalComplexWeight, Complex.norm_exp, Real.rpow_def_of_pos hw]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  rw [mul_comm]

theorem criticalComplexWeight_hasDerivAt (w : ℝ) (z : ℂ) :
    HasDerivAt (criticalComplexWeight w)
      (criticalComplexWeight w z * (Real.log w : ℂ)) z := by
  simpa only [criticalComplexWeight, one_mul] using
    ((hasDerivAt_id z).mul_const (Real.log w : ℂ)).cexp

@[simp]
theorem criticalComplexWeight_zero (w : ℝ) : criticalComplexWeight w 0 = 1 := by
  simp [criticalComplexWeight]

end

end SingularClosure
