import HXYThreeSpaces.BanachForward

/-!
# Frozen candidate C1: independent reverse implication and equivalence

The extension is bounded and matches all moments. Positivity is not assumed.
The signed Bernstein test gives V_N <= norm L for every N, hence native RH.
External Lean 4.33.0 compilation and theorem-level audit remain required.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open RH_HilbertLimit RH_HilbertLimit.TwoRoutes

namespace HXYThreeSpaces

/-- Polynomial restriction, with its real-linear structure explicit. -/
def polynomialRestriction : Polynomial ℝ →ₗ[ℝ] C(HausdorffInterval, ℝ) where
  toFun p :=
    ⟨fun q => p.eval (q : ℝ), p.continuous.comp continuous_subtype_val⟩
  map_add' p q := by
    ext x
    exact Polynomial.eval_add
  map_smul' c p := by
    ext x
    simp [RingHom.id_apply, Polynomial.smul_eq_C_mul]

@[simp] theorem polynomialRestriction_apply (p : Polynomial ℝ)
    (q : HausdorffInterval) : polynomialRestriction p q = p.eval (q : ℝ) := rfl

@[simp] theorem polynomialRestriction_one :
    polynomialRestriction (1 : Polynomial ℝ) = 1 := by
  ext q
  simp

@[simp] theorem polynomialRestriction_monomial (n : ℕ) (c : ℝ) :
    polynomialRestriction (Polynomial.monomial n c) = c • intervalMonomial n := by
  ext q
  simp [intervalMonomial]

/-- Matching all monomials matches the original functional on every polynomial. -/
theorem extension_polynomial (u : ℕ → ℝ)
    (L : C(HausdorffInterval, ℝ) →L[ℝ] ℝ)
    (hmom : ∀ n : ℕ, L (intervalMonomial n) = u n) (p : Polynomial ℝ) :
    L (polynomialRestriction p) = momentFunctional u p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simpa only [map_add, hp, hq]
  | monomial n c =>
      rw [polynomialRestriction_monomial, map_smul, hmom n,
        momentFunctional_monomial]
      rfl

theorem banachExt_iff_polynomialExtension :
    BanachExt ↔ ∃ L : C(HausdorffInterval, ℝ) →L[ℝ] ℝ,
      ∀ p : Polynomial ℝ,
        L (polynomialRestriction p) = momentFunctional actualNormalizedMoment p := by
  constructor
  · rintro ⟨L, hmom⟩
    exact ⟨L, extension_polynomial actualNormalizedMoment L hmom⟩
  · rintro ⟨L, hpoly⟩
    refine ⟨L, fun n => ?_⟩
    simpa only [polynomialRestriction_monomial, one_smul,
      momentFunctional_monomial, one_mul] using hpoly (Polynomial.monomial n 1)

private def unitSign (x : ℝ) : ℝ := if 0 ≤ x then 1 else -1

private theorem abs_unitSign (x : ℝ) : |unitSign x| = 1 := by
  by_cases hx : 0 ≤ x <;> simp [unitSign, hx]

private theorem unitSign_mul (x : ℝ) : unitSign x * x = |x| := by
  by_cases hx : 0 ≤ x
  · simp [unitSign, hx, abs_of_nonneg hx]
  · simp [unitSign, hx, abs_of_neg (lt_of_not_ge hx)]

def intervalBernstein (N j : ℕ) : C(HausdorffInterval, ℝ) :=
  polynomialRestriction (bernsteinPolynomial ℝ N j)

theorem intervalBernstein_nonneg (N j : ℕ) (q : HausdorffInterval) :
    0 ≤ intervalBernstein N j q := by
  change 0 ≤ (bernsteinPolynomial ℝ N j).eval (q : ℝ)
  simp only [bernsteinPolynomial, Polynomial.eval_mul, Polynomial.eval_natCast,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_sub, Polynomial.eval_one]
  exact mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg q.property.1 _))
    (pow_nonneg (sub_nonneg.mpr q.property.2) _)

theorem intervalBernstein_sum (N : ℕ) :
    (∑ j ∈ Finset.range (N + 1), intervalBernstein N j) = 1 := by
  simpa only [map_sum, polynomialRestriction_one, intervalBernstein] using
    congrArg polynomialRestriction (bernsteinPolynomial.sum ℝ N)

private def signedBernstein (u : ℕ → ℝ) (N : ℕ) : C(HausdorffInterval, ℝ) :=
  ∑ j ∈ Finset.range (N + 1),
    unitSign (bernsteinWeight u N j) • intervalBernstein N j

private theorem signedBernstein_norm_le (u : ℕ → ℝ) (N : ℕ) :
    ‖signedBernstein u N‖ ≤ 1 := by
  apply (ContinuousMap.norm_le _ zero_le_one).mpr
  intro q
  simp only [signedBernstein, ContinuousMap.sum_apply,
    ContinuousMap.smul_apply, smul_eq_mul]
  calc
    _ ≤ ∑ j ∈ Finset.range (N + 1),
        ‖unitSign (bernsteinWeight u N j) * intervalBernstein N j q‖ :=
      norm_sum_le _ _
    _ = ∑ j ∈ Finset.range (N + 1), intervalBernstein N j q := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Real.norm_eq_abs, abs_mul, abs_unitSign, one_mul,
        abs_of_nonneg (intervalBernstein_nonneg N j q)]
    _ = 1 := by
      have h := congrArg (fun f : C(HausdorffInterval, ℝ) => f q)
        (intervalBernstein_sum N)
      simpa using h

private theorem signedBernstein_value (u : ℕ → ℝ)
    (L : C(HausdorffInterval, ℝ) →L[ℝ] ℝ)
    (hmom : ∀ n : ℕ, L (intervalMonomial n) = u n) (N : ℕ) :
    L (signedBernstein u N) = rowVariation u N := by
  simp only [signedBernstein, rowVariation, map_sum, map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j hj
  rw [intervalBernstein, extension_polynomial u L hmom,
    momentFunctional_bernsteinPolynomial]
  exact unitSign_mul _

/-- A bounded extension forces one uniform bound for all Bernstein degrees. -/
theorem variation_le_extension_norm (u : ℕ → ℝ)
    (L : C(HausdorffInterval, ℝ) →L[ℝ] ℝ)
    (hmom : ∀ n : ℕ, L (intervalMonomial n) = u n) (N : ℕ) :
    rowVariation u N ≤ ‖L‖ := by
  calc
    rowVariation u N = ‖L (signedBernstein u N)‖ := by
      rw [signedBernstein_value u L hmom N, Real.norm_eq_abs,
        abs_of_nonneg (rowVariation_nonneg u N)]
    _ ≤ ‖L‖ := L.unit_le_opNorm (signedBernstein u N) (signedBernstein_norm_le u N)

/-- No positivity premise: boundedness alone implies the literal native RH. -/
theorem nativeRH_of_banachExt (h : BanachExt) : _root_.RiemannHypothesis := by
  obtain ⟨L, hmom⟩ := h
  obtain ⟨B, hB⟩ := exists_nat_gt ‖L‖
  apply canonical_actual_natural_bound_iff_nativeRH_constructed.mp
  refine ⟨B, fun n => ?_⟩
  exact (variation_le_extension_norm actualNormalizedMoment L hmom n).trans hB.le

/-- Frozen C1 equivalence; no RH or extension premise remains outside the iff. -/
theorem nativeRH_iff_banachExt : _root_.RiemannHypothesis ↔ BanachExt :=
  ⟨banachExt_of_nativeRH, nativeRH_of_banachExt⟩

end HXYThreeSpaces
