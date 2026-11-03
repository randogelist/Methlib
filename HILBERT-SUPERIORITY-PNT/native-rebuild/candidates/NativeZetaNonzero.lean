import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
Conditional Möbius-inverse route for strict right-half-plane nonvanishing.

The missing analytic endpoint is an unconditional proof that actual zeta
multiplied by the actual Möbius L-series is one for every s with 1 < s.re.
That product identity must establish absolute convergence, convolution, and
identification of the zeta L-series without using the nonvanishing endpoint.
It is an explicit theorem premise here, not an axiom or a proved fact.

This candidate has not been compiled or axiom-audited. Recursive declaration
dependencies require inspection; import and source-level name checks do not
establish proof-term independence.
-/

noncomputable section

namespace HVRNativeZetaNonzero

/-- The L-series of the actual integer-valued Möbius arithmetic function. -/
def moebiusLSeries (s : ℂ) : ℂ :=
  LSeries (fun n : ℕ => (ArithmeticFunction.moebius n : ℂ)) s

/-- The exact unproved analytic bridge needed by this route. -/
def RightHalfPlaneMoebiusInverse : Prop :=
  ∀ s : ℂ, 1 < s.re → riemannZeta s * moebiusLSeries s = 1

/-- A pointwise Möbius inverse identity rules out a zero of actual zeta. -/
theorem zeta_ne_zero_of_moebius_inverse (s : ℂ)
    (hinv : riemannZeta s * moebiusLSeries s = 1) :
    riemannZeta s ≠ 0 := by
  intro hz
  have hfalse : (0 : ℂ) = 1 := by
    simpa only [hz, zero_mul] using hinv
  exact zero_ne_one hfalse

/-- Conditional strict half-plane endpoint with its missing bridge explicit. -/
theorem zeta_ne_zero_of_one_lt_re_of_moebius_inverse
    (hinv : RightHalfPlaneMoebiusInverse) {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s ≠ 0 := by
  exact zeta_ne_zero_of_moebius_inverse s (hinv s hs)

end HVRNativeZetaNonzero
