import NativeChebyshevBound
import HVR_PrimeLogDensity
import Mathlib.MeasureTheory.Integral.ExpDecay

noncomputable section
open Filter Asymptotics MeasureTheory HVRPrimeLogDensity

/-!
Real logarithmic-coordinate estimates for the actual Chebyshev prime count.
The integrability theorem provides a real majorant for future use; complex
integrability and the Mellin/Laplace change of variables remain separate.
Mathlib proof dependencies need the project's route-independence review.
No Lean execution was performed in preparing this candidate.
-/
namespace HVRPrimeCountExpGrowth

/-- The exact logarithmic prime mass grows at most as exp(u). -/
theorem logPrimeMass_isBigO_exp :
    logPrimeMass =O[atTop] (fun u : ℝ => Real.exp ((1 : ℝ) * u)) := by
  apply Asymptotics.IsBigO.of_bound (Real.log 4)
  apply Filter.Eventually.of_forall
  intro u
  have hn : 0 ≤ logPrimeMass u := Chebyshev.theta_nonneg (Real.exp u)
  have hb : logPrimeMass u ≤ Real.log 4 * Real.exp u :=
    HVRNativeChebyshevBound.theta_le_log4_mul_x_native (le_of_lt (Real.exp_pos u))
  simpa only [one_mul, Real.norm_eq_abs,
    abs_of_nonneg hn, abs_of_pos (Real.exp_pos u)] using hb

/-- The positive real prime-mass majorant is integrable at infinity. -/
theorem logPrimeMass_integrableOn_exp_neg_mul (b : ℝ) (hb : 1 < b) :
    IntegrableOn (fun u : ℝ => Real.exp (-b * u) * logPrimeMass u)
      (Set.Ici 0) volume := by
  have hdecay : IntegrableOn (fun u : ℝ => Real.exp (-(b - 1) * u))
      (Set.Ioi (-1)) volume :=
    exp_neg_integrableOn_Ioi (-1) (sub_pos.mpr hb)
  have hdecay0 : IntegrableOn (fun u : ℝ => Real.exp (-(b - 1) * u))
      (Set.Ici 0) volume := by
    apply hdecay.mono_set
    intro u hu
    simp only [Set.mem_Ici] at hu
    simp only [Set.mem_Ioi]
    linarith
  have hmajor : IntegrableOn (fun u : ℝ => Real.log 4 * Real.exp (-(b - 1) * u))
      (Set.Ici 0) volume := hdecay0.const_mul (Real.log 4)
  have hcont : Continuous (fun u : ℝ => Real.exp (-b * u)) := by fun_prop
  have hmeas : Measurable (fun u : ℝ => Real.exp (-b * u) * logPrimeMass u) :=
    hcont.measurable.mul logPrimeMass_monotone.measurable
  apply Integrable.mono' hmajor hmeas.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro u
  have hn : 0 ≤ logPrimeMass u := Chebyshev.theta_nonneg (Real.exp u)
  have hbnd : logPrimeMass u ≤ Real.log 4 * Real.exp u :=
    HVRNativeChebyshevBound.theta_le_log4_mul_x_native (le_of_lt (Real.exp_pos u))
  have hexp : Real.exp (-b * u) * Real.exp u = Real.exp (-(b - 1) * u) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    ‖Real.exp (-b * u) * logPrimeMass u‖ =
        Real.exp (-b * u) * logPrimeMass u := by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (le_of_lt (Real.exp_pos _)) hn)]
    _ ≤ Real.exp (-b * u) * (Real.log 4 * Real.exp u) :=
      mul_le_mul_of_nonneg_left hbnd (le_of_lt (Real.exp_pos _))
    _ = Real.log 4 * Real.exp (-(b - 1) * u) := by rw [← hexp]; ring

end HVRPrimeCountExpGrowth
