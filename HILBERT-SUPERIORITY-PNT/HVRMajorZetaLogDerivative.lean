/- Adapted from the earlier HVR implementation, itself based on Mathlib4
   Mathlib/NumberTheory/LSeries/Dirichlet.lean, Copyright 2024 Michael Stoll,
   Apache License 2.0. See the accompanying Mathlib license. -/
import NextMangoldtDivisorSum
import NextSummability
import IntegratedZetaNonzero
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Tactic

/-!
The native divisor-sum identity gives the convolution coefficients. Fiberwise
regrouping and differentiation under a locally uniform sum give the product
and derivative on the open right half-plane.
-/

noncomputable section
set_option maxHeartbeats 1000000
open scoped LSeries.notation ArithmeticFunction.vonMangoldt ArithmeticFunction.zeta
open LSeries Nat Complex ArithmeticFunction

namespace HVRMajorZetaLogDerivative

theorem convolution_vonMangoldt_zeta_native : (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) ⍟ (fun n : ℕ => (ArithmeticFunction.zeta n : ℂ)) = (fun n : ℕ => Complex.log (n : ℂ)) := by
  ext n
  simpa [apply_ite, LSeries.convolution_def, -ArithmeticFunction.vonMangoldt_mul_zeta]
    using congr_arg (ofReal <| · n)
      HVRNextMangoldtDivisorSum.vonMangoldt_mul_zeta_native

theorem convolution_vonMangoldt_const_one_native : (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) ⍟ 1 = (fun n : ℕ => Complex.log (n : ℂ)) := by
  calc
    _ = (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) ⍟
        (fun n : ℕ => (ArithmeticFunction.zeta n : ℂ)) := by
      apply LSeries.convolution_congr (fun _ => rfl)
      intro n hn
      exact (HVRNativeOneZetaSummability.positive_zeta_coefficient hn).symm
    _ = _ := convolution_vonMangoldt_zeta_native

/-- For the constant coefficients, the line at x = (1 + Re(s))/2 supplies
the summable majorant for locally uniform differentiation at s. Adapted from
Mathlib/NumberTheory/LSeries/Deriv.lean (Michael Stoll, Apache 2.0). -/
theorem deriv_one_series {s : ℂ} (hs : 1 < s.re) :
    deriv (L 1) s = -L (logMul 1) s := by
  let x : ℝ := (1 + s.re) / 2
  have hx : 1 < x := by dsimp [x]; linarith
  have hxs : x < s.re := by dsimp [x]; linarith
  let U : Set ℂ := {z | x < z.re}
  have hsum : Summable (fun n => ‖term (1 : ℕ → ℂ) (x : ℂ) n‖) :=
    summable_norm_iff.mpr <|
      HVRNativeOneZetaSummability.one_summable (s := (x : ℂ)) (by simpa using hx)
  have hdiff (n : ℕ) : DifferentiableOn ℂ (term (1 : ℕ → ℂ) · n) U :=
    fun z _ => (hasDerivAt_term _ n z).differentiableAt.differentiableWithinAt
  have hopen : IsOpen U := isOpen_lt continuous_const continuous_re
  have hbound (n : ℕ) (z : ℂ) (hz : z ∈ U) :
      ‖term (1 : ℕ → ℂ) z n‖ ≤ ‖term 1 (x : ℂ) n‖ :=
    norm_term_le_of_re_le_re _ (by simpa using (show x < z.re from hz).le) n
  have h := hasSum_deriv_of_summable_norm hsum hdiff hopen hbound (show s ∈ U from hxs)
  simp_rw [(hasDerivAt_term (1 : ℕ → ℂ) _ _).deriv] at h
  have hfun : LSeries (1 : ℕ → ℂ) =
      (fun w : ℂ => ∑' n : ℕ, term (1 : ℕ → ℂ) w n) := by
    funext w
    rfl
  rw [hfun]
  simpa only [LSeries, tsum_neg] using! h.tsum_eq.symm

/-- The coefficient vectors agree at every index, including zero. -/
theorem logMul_one_coefficients :
    logMul (1 : ℕ → ℂ) = (fun n : ℕ => Complex.log (n : ℂ)) := by
  funext n
  simp [logMul]

/-- The actual von Mangoldt L-series equals minus the logarithmic derivative
of the constant-one L-series in the open half-plane. -/
theorem vonMangoldt_LSeries_eq_neg_logDeriv_one {s : ℂ} (hs : 1 < s.re) :
    L (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) s = -deriv (L 1) s / L 1 s := by
  have h1 : LSeriesSummable (1 : ℕ → ℂ) s := HVRNativeOneZetaSummability.one_summable hs
  have hΛ : LSeriesSummable ((fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ))) s :=
    HVRNextSummability.vonMangoldt_lseries_summable hs
  have hne : L 1 s ≠ 0 := by
    rw [HVRNativeOneZetaSummability.one_series_eq_zeta hs]
    exact HVRIntegratedZetaNonzero.zeta_ne_zero_of_one_lt_re hs
  rw [eq_div_iff hne,
    ← HVRNativeOneZetaSummability.convolution_sum hΛ h1,
    convolution_vonMangoldt_const_one_native, deriv_one_series hs, neg_neg]
  exact congrArg (fun f : ℕ → ℂ => LSeries f s) logMul_one_coefficients.symm

/-- The actual von Mangoldt L-series equals minus ζ'/ζ for Re(s) > 1. -/
theorem vonMangoldt_LSeries_eq_neg_logDeriv_zeta {s : ℂ} (hs : 1 < s.re) :
    L (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) s = -deriv riemannZeta s / riemannZeta s := by
  have hderiv : deriv (L 1) s = deriv riemannZeta s := by
    refine Filter.EventuallyEq.deriv_eq <| Filter.eventuallyEq_iff_exists_mem.mpr ?_
    exact ⟨{z | 1 < z.re}, (isOpen_lt continuous_const continuous_re).mem_nhds hs,
      fun _ ↦ HVRNativeOneZetaSummability.one_series_eq_zeta⟩
  rw [vonMangoldt_LSeries_eq_neg_logDeriv_one hs,
    HVRNativeOneZetaSummability.one_series_eq_zeta hs, hderiv]

end HVRMajorZetaLogDerivative
