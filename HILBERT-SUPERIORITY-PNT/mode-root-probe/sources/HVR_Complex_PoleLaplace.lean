import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic

noncomputable section
open MeasureTheory

/-! The elementary complex exponential integral used to subtract the pole
from the actual prime-count Laplace transform. This is a candidate requiring
external Lean compilation and theorem-level axiom audit. -/
namespace HVRComplexPoleLaplace

/-- Exponential decay on the positive real half-line. -/
theorem exponential_integrable (z : ℂ) (hz : 0 < z.re) :
    IntegrableOn (fun u : ℝ => Complex.exp (-z * (u : ℂ))) (Set.Ioi 0) volume := by
  have hzneg : (-z).re < 0 := by
    rw [Complex.neg_re]
    linarith
  exact integrableOn_exp_mul_complex_Ioi hzneg 0

/-- Laplace transform of the constant one function on the positive half-line. -/
theorem exponential_integral_eq_inv (z : ℂ) (hz : 0 < z.re) :
    (∫ u : ℝ in Set.Ioi 0, Complex.exp (-z * (u : ℂ))) = z⁻¹ := by
  have hzneg : (-z).re < 0 := by
    rw [Complex.neg_re]
    linarith
  simpa using (integral_exp_mul_complex_Ioi (a := -z) hzneg 0)

end HVRComplexPoleLaplace
