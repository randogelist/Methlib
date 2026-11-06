import HXYThreeSpaces.HilbertForward
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# Frozen C2 reverse implication and biconditional

Positive-contraction polynomial evaluation gives nonnegative Bernstein rows,
then the retained actual H00 closure gives native RH.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter RH_HilbertLimit RH_HilbertLimit.TwoRoutes
open scoped BigOperators Topology ComplexConjugate InnerProductSpace

namespace HXYThreeSpaces

section Reverse

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Evaluation of every real polynomial is determined by the stated moments. -/
theorem momentFunctional_eq_re_inner_aeval
    (u : ℕ → ℝ) (T : H →L[ℂ] H) (v : H)
    (hmom : ∀ n : ℕ, inner ℂ v ((T ^ n) v) = (u n : ℂ))
    (p : Polynomial ℝ) :
    momentFunctional u p = (inner ℂ v ((Polynomial.aeval T p) v)).re := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simp only [map_add, ContinuousLinearMap.add_apply, inner_add_right,
        Complex.add_re, hp, hq]
  | monomial n c =>
      have hOne (x : H) : (1 : H →L[ℂ] H) x = x := rfl
      rw [momentFunctional_monomial, Polynomial.aeval_monomial,
        Algebra.algebraMap_eq_smul_one,
        ← algebraMap_smul ℂ c (1 : H →L[ℂ] H)]
      simp only [ContinuousLinearMap.mul_apply,
        ContinuousLinearMap.smul_apply, hOne, inner_smul_right, hmom,
        Complex.coe_algebraMap, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, sub_zero]

/-- A positive contraction makes every Bernstein polynomial positive. -/
theorem operator_bernsteinWeight_nonnegative
    (u : ℕ → ℝ) (T : H →L[ℂ] H) (v : H)
    (hT : T.IsPositive) (hI : (1 - T).IsPositive)
    (hmom : ∀ n : ℕ, inner ℂ v ((T ^ n) v) = (u n : ℂ))
    (N j : ℕ) : 0 ≤ bernsteinWeight u N j := by
  have hT0 : 0 ≤ T := (ContinuousLinearMap.nonneg_iff_isPositive T).mpr hT
  have hI0 : 0 ≤ (1 - T) :=
    (ContinuousLinearMap.nonneg_iff_isPositive (1 - T)).mpr hI
  have hcomm : Commute T (1 - T) := by
    show T * (1 - T) = (1 - T) * T
    simp only [mul_sub, sub_mul, mul_one, one_mul]
  have hprod : 0 ≤ T ^ j * (1 - T) ^ (N - j) :=
    Commute.mul_nonneg (CStarAlgebra.pow_nonneg hT0 j)
      (CStarAlgebra.pow_nonneg hI0 (N - j)) (hcomm.pow_pow j (N - j))
  have hp := ContinuousLinearMap.IsPositive.re_inner_nonneg_right
    ((ContinuousLinearMap.nonneg_iff_isPositive
      (T ^ j * (1 - T) ^ (N - j))).mp hprod) v
  simp only [RCLike.re_to_complex] at hp
  have hpoly : Polynomial.aeval T (bernsteinPolynomial ℝ N j) =
      (Nat.choose N j : ℝ) • (T ^ j * (1 - T) ^ (N - j)) := by
    have hbern : bernsteinPolynomial ℝ N j =
        Polynomial.C (Nat.choose N j : ℝ) * Polynomial.X ^ j *
          (1 - Polynomial.X) ^ (N - j) := by
      simp [bernsteinPolynomial]
    rw [hbern]
    simp only [map_mul, map_pow, map_sub, map_one,
      Polynomial.aeval_C, Polynomial.aeval_X, Algebra.algebraMap_eq_smul_one,
      smul_mul_assoc, one_mul]
  rw [← momentFunctional_bernsteinPolynomial,
    momentFunctional_eq_re_inner_aeval u T v hmom, hpoly,
    ← algebraMap_smul ℂ (Nat.choose N j : ℝ) (T ^ j * (1 - T) ^ (N - j)),
    ContinuousLinearMap.smul_apply, inner_smul_right]
  simpa only [Complex.coe_algebraMap, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] using
    mul_nonneg (Nat.cast_nonneg (Nat.choose N j)) hp

end Reverse

/-- Frozen C2 reverse endpoint; no spectral-measure premise is added. -/
theorem nativeRH_of_hilbertRep (h : HilbertRep) : _root_.RiemannHypothesis := by
  rcases h with ⟨H, instNorm, h⟩
  letI := instNorm
  rcases h with ⟨instInner, h⟩
  letI := instInner
  rcases h with ⟨instComplete, h⟩
  letI := instComplete
  rcases h with ⟨T, v, _hself, hT, hI, _hv, hmom⟩
  apply nativeRH_of_H00_route_one
  apply H00_of_actual_weights_nonnegative
  intro N j _hj
  exact operator_bernsteinWeight_nonnegative actualNormalizedMoment T v hT hI hmom N j

/-- Frozen C2 biconditional. -/
theorem nativeRH_iff_hilbertRep : _root_.RiemannHypothesis ↔ HilbertRep :=
  ⟨hilbertRep_of_nativeRH, nativeRH_of_hilbertRep⟩

end HXYThreeSpaces
