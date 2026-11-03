/- Adapted from the earlier HVR implementation, itself based on Mathlib4
   Mathlib/NumberTheory/LSeries/Dirichlet.lean, Copyright 2024 Michael Stoll,
   Apache License 2.0. See the accompanying Mathlib license. -/
import HVRSimpleMoebiusBound
import NativeZetaNonzero
import NativeOneZetaSummability
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
Source candidate: the previously conditional Möbius inverse bridge follows
from absolute convergence and the generic arithmetic-function convolution.
The proof uses bounded coefficient summability, the Möbius inverse identity, convolution
and identification of the zeta L-series, not its named nonvanishing theorem.
External compilation, axiom audit, and dependency inspection are outstanding.
-/

noncomputable section
set_option maxHeartbeats 1000000
open scoped LSeries.notation ArithmeticFunction.zeta ArithmeticFunction.Moebius
open LSeries ArithmeticFunction

namespace HVRMajorZetaNonzero

/-- Möbius series summability from bounded coefficients, without invoking
`ArithmeticFunction.LSeriesSummable_moebius_iff`. -/
theorem moebiusLSeries_summable {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable ((fun n : ℕ => (ArithmeticFunction.moebius n : ℂ))) s := by
  apply LSeriesSummable_of_bounded_of_one_lt_re (m := 1) ?_ hs
  intro n hn
  norm_cast
  exact HVRSimpleMoebiusBound.abs_moebius_le_one n

theorem zetaLSeries_mul_moebiusLSeries {s : ℂ} (hs : 1 < s.re) :
    L (fun n : ℕ => (ArithmeticFunction.zeta n : ℂ)) s * L (fun n : ℕ => (ArithmeticFunction.moebius n : ℂ)) s = 1 := by
  rw [← LSeries_convolution' (HVRNativeOneZetaSummability.arithmetic_zeta_summable hs)
    (moebiusLSeries_summable hs)]
  simp [← natCoe_apply, ← intCoe_apply, coe_mul, one_eq_delta, LSeries_delta, -zeta_apply]

theorem rightHalfPlaneMoebiusInverse : HVRNativeZetaNonzero.RightHalfPlaneMoebiusInverse := by
  intro s hs
  have h := zetaLSeries_mul_moebiusLSeries hs
  rw [ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs] at h
  exact h

theorem zeta_ne_zero_of_one_lt_re {s : ℂ} (hs : 1 < s.re) : riemannZeta s ≠ 0 :=
  HVRNativeZetaNonzero.zeta_ne_zero_of_one_lt_re_of_moebius_inverse
    rightHalfPlaneMoebiusInverse hs

end HVRMajorZetaNonzero
