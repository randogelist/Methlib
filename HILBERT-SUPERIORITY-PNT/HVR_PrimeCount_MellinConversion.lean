import HVR_PrimeCount_MellinDefs
import Mathlib.NumberTheory.Chebyshev
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
open MeasureTheory
open HVRPrimeCountMellin HVRPrimeZetaSplit HVRZetaLogDerivative

/-! Existing prime-theta identification and change-of-variables lemmas moved
upstream unchanged to eliminate the direct-mode import cycle. Candidate;
external Lean compilation and theorem-level audit remain required. -/
namespace HVRPrimeCountGrowth

theorem primeTheta_eq_chebyshev (x : ℝ) :
    primeTheta x = (Chebyshev.theta x : ℂ) := by
  have hset : Finset.Icc 1 ⌊x⌋₊ = Finset.Ioc 0 ⌊x⌋₊ := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have hreal : (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, primeCoefficient n) =
      Chebyshev.theta x := by
    rw [Chebyshev.theta, ← hset]
    simp only [primeCoefficient, Finset.sum_filter]
  unfold primeTheta
  simp only [primeCoefficientC, ← Complex.ofReal_sum, hreal]

end HVRPrimeCountGrowth

namespace HVRPrimeCountLogSubstitution

theorem exp_image_pos_halfline :
    Real.exp '' Set.Ioi (0 : ℝ) = Set.Ioi (1 : ℝ) := by
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    change 1 < Real.exp u
    have hu' : (0 : ℝ) < u := hu
    simpa only [Real.exp_zero] using (Real.exp_lt_exp.mpr hu')
  · intro hx
    have hx' : (1 : ℝ) < x := hx
    have hxpos : (0 : ℝ) < x := by linarith
    refine ⟨Real.log x, ?_, Real.exp_log hxpos⟩
    exact Real.log_pos hx'

/-- The factor contributed by the exponential Jacobian combines with the
complex Mellin power. -/
theorem exp_mul_mellin_power (u : ℝ) (s : ℂ) :
    (Real.exp u : ℂ) * (Real.exp u : ℂ) ^ (-(s + 1)) =
      Complex.exp (-s * (u : ℂ)) := by
  have he : (Real.exp u : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.exp_pos u))
  rw [Complex.cpow_def_of_ne_zero he]
  have hlog : Complex.log (Real.exp u : ℂ) = (u : ℂ) := by
    simpa only [Real.log_exp] using
      (Complex.ofReal_log (le_of_lt (Real.exp_pos u))).symm
  rw [hlog, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  ring

/-- Exponential substitution in the actual prime-count Mellin integral. -/
theorem primeThetaMellin_eq_exp_integral (s : ℂ) :
    primeThetaMellin s =
      ∫ u : ℝ in Set.Ioi 0, primeTheta (Real.exp u) * Complex.exp (-s * (u : ℂ)) := by
  have hsub := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
    (s := Set.Ioi (0 : ℝ)) (f := Real.exp) (f' := Real.exp)
    measurableSet_Ioi
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
    Real.exp_strictMono.injective.injOn
    (fun x : ℝ => primeTheta x * (x : ℂ) ^ (-(s + 1)))
  rw [exp_image_pos_halfline] at hsub
  unfold primeThetaMellin
  rw [hsub]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with u
  simp only [abs_of_pos (Real.exp_pos u), Complex.real_smul]
  calc
    (Real.exp u : ℂ) * (primeTheta (Real.exp u) * (Real.exp u : ℂ) ^ (-(s + 1))) =
        primeTheta (Real.exp u) * ((Real.exp u : ℂ) * (Real.exp u : ℂ) ^ (-(s + 1))) := by ring
    _ = primeTheta (Real.exp u) * Complex.exp (-s * (u : ℂ)) := by
      rw [exp_mul_mellin_power]

end HVRPrimeCountLogSubstitution
