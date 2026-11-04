import HVRComplexExpIntegralDirect

noncomputable section
open MeasureTheory

/-! The elementary complex exponential integral used to subtract the pole
from the actual prime-count Laplace transform. These declarations preserve the
original exact signatures while delegating to the direct one-variable majorant
and improper-integral proof in HVRComplexExpIntegralDirect. This replacement
and the rewritten PNT root require external compilation, theorem-level axiom
audits, and dependency diagnostics. -/
namespace HVRComplexPoleLaplace

/-- Exponential decay on the positive real half-line. -/
theorem exponential_integrable (z : ℂ) (hz : 0 < z.re) :
    IntegrableOn (fun u : ℝ => Complex.exp (-z * (u : ℂ))) (Set.Ioi 0) volume :=
  HVRComplexExpIntegralDirect.exponential_integrable_direct z hz

/-- Laplace transform of the constant one function on the positive half-line. -/
theorem exponential_integral_eq_inv (z : ℂ) (hz : 0 < z.re) :
    (∫ u : ℝ in Set.Ioi 0, Complex.exp (-z * (u : ℂ))) = z⁻¹ :=
  HVRComplexExpIntegralDirect.exponential_integral_eq_inv_direct z hz

end HVRComplexPoleLaplace
