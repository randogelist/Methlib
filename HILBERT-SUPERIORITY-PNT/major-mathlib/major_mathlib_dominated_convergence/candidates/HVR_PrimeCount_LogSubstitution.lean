import HVR_PrimeCount_MellinGerm
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

noncomputable section
open MeasureTheory
open HVRPrimeCountMellin HVRPrimeCountMellinGerm HVRPrimeZetaSplit
open HVRSmoothingAnalyticGerms

/-!
Candidate change of variables for the actual prime-count Mellin integral.
Bochner integrals are used throughout; this module does not itself assert
integrability, the pole-subtracted Laplace integral, or the Fourier limits.
No local Lean run was performed. -/
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

/-- The unregularized exponential integral has the same pole-subtracted
expression as the previously certified analytic germ. -/
theorem exp_integral_sub_pole_eq_regularPartAt
    (sigma t : ℝ) (hsigma : 1 < sigma) :
    (∫ u : ℝ in Set.Ioi 0,
      primeTheta (Real.exp u) * Complex.exp (-(zetaPoint sigma t) * (u : ℂ))) -
        (zetaPoint sigma t - 1)⁻¹ = regularPartAt (zetaPoint sigma t) := by
  rw [← primeThetaMellin_eq_exp_integral]
  exact primeThetaMellin_sub_pole_eq_regularPartAt_of_growth sigma t hsigma

end HVRPrimeCountLogSubstitution
