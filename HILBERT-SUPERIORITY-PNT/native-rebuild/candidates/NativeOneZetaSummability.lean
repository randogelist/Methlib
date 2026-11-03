import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Tactic

/-!
Specialized convergence replacements for the HVR zeta bridge. These statements
only prove convergence on the strict right half-plane and the one-sided
abscissa bound required by differentiation. They use the generic Mathlib
bounded-coefficient convergence theorem and generic abscissa infrastructure.
They do not assert the converses or the exact value of an abscissa.

These are source candidates until checked by the external cached Lean compiler,
named-theorem axiom audit, and declaration-dependency diagnostic.
-/

noncomputable section

namespace HVRNativeOneZetaSummability

/-- The constant-one L-series converges absolutely on the half-plane. -/
theorem one_summable {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (1 : ℕ → ℂ) s := by
  apply LSeriesSummable_of_bounded_of_one_lt_re (m := 1) ?_ hs
  intro n hn
  simp

/-- The arithmetic zeta L-series converges absolutely on the half-plane. -/
theorem arithmetic_zeta_summable {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n : ℕ => (ArithmeticFunction.zeta n : ℂ)) s := by
  have heq : ∀ {n : ℕ}, n ≠ 0 →
      (1 : ℕ → ℂ) n = (ArithmeticFunction.zeta n : ℂ) := by
    intro n hn
    simpa using (ArithmeticFunction.const_one_eq_zeta (R := ℂ) hn)
  exact (LSeriesSummable_congr s heq).mp (one_summable hs)

/-- The one-sided abscissa bound sufficient for termwise differentiation. -/
theorem one_abscissa_lt {s : ℂ} (hs : 1 < s.re) :
    LSeries.abscissaOfAbsConv (1 : ℕ → ℂ) < s.re := by
  have hbound : LSeries.abscissaOfAbsConv (1 : ℕ → ℂ) ≤ (1 : EReal) := by
    have h := LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
      (f := (1 : ℕ → ℂ)) (x := (1 : ℝ)) (fun y hy =>
        one_summable (s := (y : ℂ)) (by simpa using hy))
    simpa using h
  have hsE : (1 : EReal) < (s.re : EReal) := by exact_mod_cast hs
  exact hbound.trans_lt hsE

end HVRNativeOneZetaSummability
