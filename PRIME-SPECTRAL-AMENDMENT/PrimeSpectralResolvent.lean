import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Tactic

noncomputable section
open MeasureTheory

/-!
Diagonal spectral heat and resolvent series, independent of the PNT chain.
The norm-integral summability premise is an explicit analytic hypothesis;
this file does not construct the unbounded operator or prove that hypothesis
for the von Mangoldt weights.
-/
namespace PrimeSpectralResolvent

/-- One spectral mode is integrable whenever the shifted energy is positive. -/
theorem mode_integrable (a e w : ℝ) (h : 0 < w + e) :
    IntegrableOn (fun t : ℝ => a * Real.exp (-(w + e) * t))
      (Set.Ioi 0) volume := by
  have hneg : -(w + e) < 0 := by linarith
  exact (integrableOn_exp_mul_Ioi hneg 0).const_mul a

/-- The Laplace integral of a spectral mode gives its resolvent coefficient. -/
theorem mode_integral (a e w : ℝ) (h : 0 < w + e) :
    (∫ t : ℝ in Set.Ioi 0, a * Real.exp (-(w + e) * t)) = a / (w + e) := by
  have hneg : -(w + e) < 0 := by linarith
  have hexp : (∫ t : ℝ in Set.Ioi 0, Real.exp (-(w + e) * t)) = (w + e)⁻¹ := by
    simpa [div_eq_mul_inv] using (integral_exp_mul_Ioi (a := -(w + e)) hneg 0)
  rw [integral_const_mul, hexp]
  simp only [div_eq_mul_inv]

/-- Absolute-integral summability justifies exchanging the infinite spectral
sum with integration; the resulting series is the diagonal resolvent. -/
theorem spectral_resolvent_laplace
    (weight energy : ℕ → ℝ) (w : ℝ)
    (hpos : ∀ n, 0 < w + energy n)
    (hnorm : Summable (fun n : ℕ =>
      ∫ t : ℝ in Set.Ioi 0, ‖weight n * Real.exp (-(w + energy n) * t)‖)) :
    (∫ t : ℝ in Set.Ioi 0,
      ∑' n : ℕ, weight n * Real.exp (-(w + energy n) * t)) =
      ∑' n : ℕ, weight n / (w + energy n) := by
  have hi : ∀ n : ℕ, Integrable
      (fun t : ℝ => weight n * Real.exp (-(w + energy n) * t))
      (volume.restrict (Set.Ioi 0)) := by
    intro n
    exact mode_integrable (weight n) (energy n) w (hpos n)
  have hswap := integral_tsum_of_summable_integral_norm hi hnorm
  calc
    (∫ t : ℝ in Set.Ioi 0,
        ∑' n : ℕ, weight n * Real.exp (-(w + energy n) * t)) =
      ∑' n : ℕ, ∫ t : ℝ in Set.Ioi 0,
        weight n * Real.exp (-(w + energy n) * t) := hswap.symm
    _ = ∑' n : ℕ, weight n / (w + energy n) := by
      apply tsum_congr
      intro n
      exact mode_integral (weight n) (energy n) w (hpos n)

/-- The same identity with the Laplace factor outside the heat series. -/
theorem heat_series_resolvent_laplace
    (weight energy : ℕ → ℝ) (w : ℝ)
    (hpos : ∀ n, 0 < w + energy n)
    (hnorm : Summable (fun n : ℕ =>
      ∫ t : ℝ in Set.Ioi 0, ‖weight n * Real.exp (-(w + energy n) * t)‖)) :
    (∫ t : ℝ in Set.Ioi 0,
      Real.exp (-w * t) * (∑' n : ℕ, weight n * Real.exp (-energy n * t))) =
      ∑' n : ℕ, weight n / (w + energy n) := by
  have heq : (fun t : ℝ =>
      Real.exp (-w * t) * (∑' n : ℕ, weight n * Real.exp (-energy n * t))) =
      (fun t : ℝ => ∑' n : ℕ, weight n * Real.exp (-(w + energy n) * t)) := by
    funext t
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    rw [mul_left_comm (Real.exp (-w * t)) (weight n) (Real.exp (-energy n * t))]
    rw [← Real.exp_add]
    have harg : -w * t + -energy n * t = -(w + energy n) * t := by ring
    rw [harg]
    ring
  rw [heq]
  exact spectral_resolvent_laplace weight energy w hpos hnorm

/-- A finite nonnegative spectral mass on nonnegative energies supplies the
absolute-integral summability needed for the heat/resolvent exchange. -/
theorem summable_mode_integral_norm
    (weight energy : ℕ → ℝ) (w : ℝ)
    (hw : 0 < w) (henergy : ∀ n, 0 ≤ energy n)
    (hweight : ∀ n, 0 ≤ weight n) (hsum : Summable weight) :
    Summable (fun n : ℕ =>
      ∫ t : ℝ in Set.Ioi 0, ‖weight n * Real.exp (-(w + energy n) * t)‖) := by
  have hpos (n : ℕ) : 0 < w + energy n := by
    have hn := henergy n
    linarith
  have heq (n : ℕ) :
      (∫ t : ℝ in Set.Ioi 0, ‖weight n * Real.exp (-(w + energy n) * t)‖) =
        weight n / (w + energy n) := by
    calc
      (∫ t : ℝ in Set.Ioi 0, ‖weight n * Real.exp (-(w + energy n) * t)‖) =
          ∫ t : ℝ in Set.Ioi 0, weight n * Real.exp (-(w + energy n) * t) := by
        apply integral_congr_ae
        filter_upwards [] with t
        rw [Real.norm_eq_abs, abs_of_nonneg
          (mul_nonneg (hweight n) (le_of_lt (Real.exp_pos _)))]
      _ = weight n / (w + energy n) := mode_integral _ _ _ (hpos n)
  have hres : Summable (fun n : ℕ => weight n / (w + energy n)) := by
    refine Summable.of_nonneg_of_le
      (fun n => div_nonneg (hweight n) (le_of_lt (hpos n))) ?_ (hsum.div_const w)
    intro n
    exact div_le_div_of_nonneg_left (hweight n) hw (le_add_of_nonneg_right (henergy n))
  simpa only [heq] using hres

/-- Finite positive diagonal mass yields the heat/resolvent identity from
nonnegative energies and a positive resolvent parameter. -/
theorem heat_series_resolvent_of_summable_mass
    (weight energy : ℕ → ℝ) (w : ℝ)
    (hw : 0 < w) (henergy : ∀ n, 0 ≤ energy n)
    (hweight : ∀ n, 0 ≤ weight n) (hsum : Summable weight) :
    (∫ t : ℝ in Set.Ioi 0,
      Real.exp (-w * t) * (∑' n : ℕ, weight n * Real.exp (-energy n * t))) =
      ∑' n : ℕ, weight n / (w + energy n) := by
  apply heat_series_resolvent_laplace weight energy w
  · intro n
    have hn := henergy n
    linarith
  · exact summable_mode_integral_norm weight energy w hw henergy hweight hsum

end PrimeSpectralResolvent
