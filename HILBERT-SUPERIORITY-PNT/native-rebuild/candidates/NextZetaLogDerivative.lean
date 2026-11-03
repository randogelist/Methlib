/- Adapted from the earlier HVR implementation, itself based on Mathlib4
   Mathlib/NumberTheory/LSeries/Dirichlet.lean, Copyright 2024 Michael Stoll,
   Apache License 2.0. See the accompanying Mathlib license. -/
import NextMangoldtDivisorSum
import NextSummability
import IntegratedZetaNonzero
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Tactic

/-!
Candidate derivation of the actual von Mangoldt/zeta logarithmic derivative
through the native divisor-sum identity, generic Dirichlet convolution, and
generic differentiation of L-series. The target Mathlib von Mangoldt-zeta
identities are not invoked by name. Source and any dependency claim are not
verified until an external Lean build, axiom audit and dependency inspection.
-/

noncomputable section
set_option maxHeartbeats 1000000
open scoped LSeries.notation ArithmeticFunction.vonMangoldt ArithmeticFunction.zeta
open LSeries Nat Complex ArithmeticFunction

namespace HVRNextZetaLogDerivative

theorem convolution_vonMangoldt_zeta_native : (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) ⍟ (fun n : ℕ => (ArithmeticFunction.zeta n : ℂ)) = (fun n : ℕ => Complex.log (n : ℂ)) := by
  ext n
  simpa [apply_ite, LSeries.convolution_def, -ArithmeticFunction.vonMangoldt_mul_zeta]
    using congr_arg (ofReal <| · n)
      HVRNextMangoldtDivisorSum.vonMangoldt_mul_zeta_native

theorem convolution_vonMangoldt_const_one_native : (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) ⍟ 1 = (fun n : ℕ => Complex.log (n : ℂ)) :=
  (LSeries.convolution_one_eq_convolution_zeta _).trans convolution_vonMangoldt_zeta_native

/-- The actual von Mangoldt L-series equals minus the logarithmic derivative
of the constant-one L-series in the open half-plane. -/
theorem vonMangoldt_LSeries_eq_neg_logDeriv_one {s : ℂ} (hs : 1 < s.re) :
    L (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) s = -deriv (L 1) s / L 1 s := by
  have h1 : LSeriesSummable (1 : ℕ → ℂ) s := HVRNativeOneZetaSummability.one_summable hs
  have hs' : abscissaOfAbsConv (1 : ℕ → ℂ) < s.re :=
    HVRNativeOneZetaSummability.one_abscissa_lt hs
  have hΛ : LSeriesSummable ((fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ))) s :=
    HVRNextSummability.vonMangoldt_lseries_summable hs
  have hne : L 1 s ≠ 0 := by
    rw [LSeries_one_eq_riemannZeta hs]
    exact HVRIntegratedZetaNonzero.zeta_ne_zero_of_one_lt_re hs
  rw [eq_div_iff hne,
    ← LSeries_convolution' hΛ h1,
    convolution_vonMangoldt_const_one_native, LSeries_deriv hs', neg_neg]
  exact LSeries_congr (fun _ ↦ by simp [mul_comm, logMul]) s

/-- The actual von Mangoldt L-series equals minus ζ'/ζ for Re(s) > 1. -/
theorem vonMangoldt_LSeries_eq_neg_logDeriv_zeta {s : ℂ} (hs : 1 < s.re) :
    L (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) s = -deriv riemannZeta s / riemannZeta s := by
  have hderiv : deriv (L 1) s = deriv riemannZeta s := by
    refine Filter.EventuallyEq.deriv_eq <| Filter.eventuallyEq_iff_exists_mem.mpr ?_
    exact ⟨{z | 1 < z.re}, (isOpen_lt continuous_const continuous_re).mem_nhds hs,
      fun _ ↦ LSeries_one_eq_riemannZeta⟩
  rw [vonMangoldt_LSeries_eq_neg_logDeriv_one hs,
    LSeries_one_eq_riemannZeta hs, hderiv]

end HVRNextZetaLogDerivative
