import RH_HilbertLimit.Bernstein
import RH_HilbertLimit.Growth
import Mathlib.Tactic.NormNum

/-!
# What a finite prefix of arbitrary moment data determines

UNCOMPILED CANDIDATE for the user's native Lean 4.33.0 target.
No Lean, Lake, native compiler, or CI process was run to prepare this file.
The previously passed v0.1.4 source is not modified.

These results concern arbitrary real sequences, not the actual xi sequence.
They prove exact finite-row locality and exhibit arbitrarily long prefixes
with nonnegative Bernstein rows whose continuation has root growth at least
two.  They do not rule out an actual-xi-specific finite certificate carrying
a separately proved uniform propagation argument.

Mathlib APIs inspected at tag v4.33.0:
* Polynomial.Eval.Defs: eval_add, eval_monomial, eval_mul, eval_pow.
* Polynomial.Bernstein: the definition of bernsteinPolynomial.
* Pow.Real: rpow_eq_pow, rpow_natCast_mul, rpow_le_rpow.
-/

set_option autoImplicit false
noncomputable section

open Filter
open scoped BigOperators Topology

namespace RH_HilbertLimit.FinitePrefix

/-- An in-range weight uses only moments with index at most its row index. -/
theorem bernsteinWeight_congr_prefix (u v : ℕ → ℝ) (N j : ℕ)
    (hj : j ≤ N) (h : ∀ n ≤ N, u n = v n) :
    bernsteinWeight u N j = bernsteinWeight v N j := by
  unfold bernsteinWeight
  apply congrArg (fun s : ℝ => (Nat.choose N j : ℝ) * s)
  apply Finset.sum_congr rfl
  intro r hr
  have hr' : r < N - j + 1 := Finset.mem_range.mp hr
  rw [h (j + r) (by omega)]

/-- Exact locality for total variation, with no positivity premise. -/
theorem rowVariation_congr_prefix (u v : ℕ → ℝ) (N : ℕ)
    (h : ∀ n ≤ N, u n = v n) :
    rowVariation u N = rowVariation v N := by
  unfold rowVariation
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j ≤ N := by
    have := Finset.mem_range.mp hj
    omega
  rw [bernsteinWeight_congr_prefix u v N j hj' h]

/-- The diagonal weight is the corresponding moment. -/
theorem bernsteinWeight_diagonal (u : ℕ → ℝ) (N : ℕ) :
    bernsteinWeight u N N = u N := by
  simp [bernsteinWeight]

/-- Every in-range absolute weight is bounded by its row variation. -/
theorem abs_weight_le_rowVariation (u : ℕ → ℝ) (N j : ℕ)
    (hj : j ∈ Finset.range (N + 1)) :
    |bernsteinWeight u N j| ≤ rowVariation u N := by
  change |bernsteinWeight u N j| ≤
    ∑ k ∈ Finset.range (N + 1), |bernsteinWeight u N k|
  exact Finset.single_le_sum
    (fun k _ => abs_nonneg (bernsteinWeight u N k)) hj

/-- In particular, row variation sees any large diagonal moment. -/
theorem abs_moment_le_rowVariation (u : ℕ → ℝ) (N : ℕ) :
    |u N| ≤ rowVariation u N := by
  simpa only [bernsteinWeight_diagonal] using
    abs_weight_le_rowVariation u N N
      (Finset.mem_range.mpr (Nat.lt_succ_self N))

private theorem momentFunctional_constant_one (p : Polynomial ℝ) :
    momentFunctional (fun _ : ℕ => (1 : ℝ)) p = p.eval 1 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simp only [map_add, Polynomial.eval_add, hp, hq]
  | monomial n c =>
      simp only [momentFunctional_monomial, Polynomial.eval_monomial,
        one_pow, mul_one]

/-- The constant-one moments give nonnegative rows at every degree. -/
theorem bernsteinWeight_constant_one_nonneg (N j : ℕ) :
    0 ≤ bernsteinWeight (fun _ : ℕ => (1 : ℝ)) N j := by
  rw [← momentFunctional_bernsteinPolynomial, momentFunctional_constant_one]
  simp only [bernsteinPolynomial, Polynomial.eval_mul, Polynomial.eval_natCast,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_sub, Polynomial.eval_one,
    one_pow, sub_self, mul_one]
  positivity

theorem rowVariation_constant_one (N : ℕ) :
    rowVariation (fun _ : ℕ => (1 : ℝ)) N = 1 := by
  exact (rowVariation_eq_one_iff (fun _ : ℕ => (1 : ℝ)) rfl N).mpr
    (fun j _ => bernsteinWeight_constant_one_nonneg N j)

/-- Preserve any prescribed finite prefix and replace the tail by `2^n`. -/
def exponentialTail (u : ℕ → ℝ) (K n : ℕ) : ℝ :=
  if n ≤ K then u n else (2 : ℝ) ^ n

theorem exponentialTail_agrees (u : ℕ → ℝ) (K n : ℕ) (hn : n ≤ K) :
    exponentialTail u K n = u n := by
  simp only [exponentialTail, if_pos hn]

theorem exponentialTail_zero (u : ℕ → ℝ) (K : ℕ) :
    exponentialTail u K 0 = u 0 := by
  simp [exponentialTail]

theorem exponentialTail_rowVariation_agrees (u : ℕ → ℝ) (K N : ℕ)
    (hN : N ≤ K) :
    rowVariation (exponentialTail u K) N = rowVariation u N := by
  apply rowVariation_congr_prefix
  intro n hn
  exact exponentialTail_agrees u K n (hn.trans hN)

theorem exponentialTail_rootScale_agrees (u : ℕ → ℝ) (K N : ℕ)
    (hN : N ≤ K) :
    rootScale (rowVariation (exponentialTail u K)) N =
      rootScale (rowVariation u) N := by
  simp only [rootScale, exponentialTail_rowVariation_agrees u K N hN]

/-- Beyond the unchanged prefix, a single diagonal term gives exponential size. -/
theorem exponentialTail_variation_lower (u : ℕ → ℝ) (K N : ℕ)
    (hN : K < N) :
    (2 : ℝ) ^ N ≤ rowVariation (exponentialTail u K) N := by
  have h := abs_moment_le_rowVariation (exponentialTail u K) N
  rw [exponentialTail, if_neg (not_le.mpr hN),
    abs_of_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) N)] at h
  exact h

/-- The obstruction affects the eventual root growth, not just one later row. -/
theorem exponentialTail_rootScale_lower (u : ℕ → ℝ) (K N : ℕ)
    (hN : K < N) :
    2 ≤ rootScale (rowVariation (exponentialTail u K)) N := by
  have hNpos : 0 < N := lt_of_le_of_lt (Nat.zero_le K) hN
  have hNRpos : (0 : ℝ) < N := Nat.cast_pos.mpr hNpos
  have hroot : ((2 : ℝ) ^ N) ^ ((N : ℝ)⁻¹) = 2 := by
    rw [← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2) N ((N : ℝ)⁻¹),
      mul_inv_cancel₀ (ne_of_gt hNRpos), Real.rpow_one]
  have h := Real.rpow_le_rpow
    (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) N)
    (exponentialTail_variation_lower u K N hN)
    (inv_nonneg.mpr (Nat.cast_nonneg N))
  rw [hroot] at h
  simpa only [rootScale, Real.rpow_eq_pow] using h

theorem exponentialTail_not_rootScale_tendsto_one (u : ℕ → ℝ) (K : ℕ) :
    ¬ Tendsto (rootScale (rowVariation (exponentialTail u K))) atTop (𝓝 1) := by
  intro hlimit
  have hsmall : ∀ᶠ n : ℕ in atTop,
      rootScale (rowVariation (exponentialTail u K)) n < 2 :=
    (tendsto_order.mp hlimit).2 2 (by norm_num)
  obtain ⟨n, hn, hKn⟩ := (hsmall.and (eventually_gt_atTop K)).exists
  exact (not_lt_of_ge (exponentialTail_rootScale_lower u K n hKn)) hn

theorem exponentialTail_not_subexponential (u : ℕ → ℝ) (K : ℕ)
    (hzero : u 0 = 1) :
    ¬ Subexponential (rowVariation (exponentialTail u K)) := by
  have hzero' : exponentialTail u K 0 = 1 :=
    (exponentialTail_zero u K).trans hzero
  have hone : ∀ᶠ n : ℕ in atTop,
      1 ≤ rowVariation (exponentialTail u K) n :=
    Eventually.of_forall (one_le_rowVariation (exponentialTail u K) hzero')
  intro hSG
  exact exponentialTail_not_rootScale_tendsto_one u K
    ((subexponential_iff_rootScale_one hone).mp hSG)

theorem exponentialTail_next_variation_ne_one (u : ℕ → ℝ) (K : ℕ) :
    rowVariation (exponentialTail u K) (K + 1) ≠ 1 := by
  intro hV
  have h := exponentialTail_rootScale_lower u K (K + 1) (Nat.lt_succ_self K)
  simp only [rootScale, hV, Real.rpow_eq_pow, Real.one_rpow] at h
  norm_num at h

/-- For normalized input, the very next row already contains a negative weight. -/
theorem exponentialTail_next_negative (u : ℕ → ℝ) (K : ℕ)
    (hzero : u 0 = 1) :
    ∃ j : ℕ, j ≤ K + 1 ∧ bernsteinWeight (exponentialTail u K) (K + 1) j < 0 := by
  classical
  by_contra hneg
  have hzero' : exponentialTail u K 0 = 1 :=
    (exponentialTail_zero u K).trans hzero
  have hnonneg : ∀ j ∈ Finset.range (K + 1 + 1),
      0 ≤ bernsteinWeight (exponentialTail u K) (K + 1) j := by
    intro j hj
    by_contra hjneg
    have hj' : j ≤ K + 1 := by
      have := Finset.mem_range.mp hj
      omega
    exact hneg ⟨j, hj', lt_of_not_ge hjneg⟩
  exact exponentialTail_next_variation_ne_one u K
    ((rowVariation_eq_one_iff (exponentialTail u K) hzero' (K + 1)).mpr hnonneg)

/-- No fixed number of positive rows forces global subexponential growth
for an arbitrary moment sequence.  This makes no assertion about extra
analytic structure possessed by the actual xi moments. -/
theorem arbitrarily_long_positive_prefix (K : ℕ) :
    ∃ v : ℕ → ℝ,
      v 0 = 1 ∧
      (∀ n ≤ K, v n = 1) ∧
      (∀ N ≤ K, rowVariation v N = 1) ∧
      (∀ N, K < N → 2 ≤ rootScale (rowVariation v) N) ∧
      ¬ Subexponential (rowVariation v) := by
  refine ⟨exponentialTail (fun _ : ℕ => (1 : ℝ)) K, ?_, ?_, ?_, ?_, ?_⟩
  · exact exponentialTail_zero (fun _ : ℕ => (1 : ℝ)) K
  · intro n hn
    exact exponentialTail_agrees (fun _ : ℕ => (1 : ℝ)) K n hn
  · intro N hN
    rw [exponentialTail_rowVariation_agrees (fun _ : ℕ => (1 : ℝ)) K N hN,
      rowVariation_constant_one]
  · intro N hN
    exact exponentialTail_rootScale_lower (fun _ : ℕ => (1 : ℝ)) K N hN
  · exact exponentialTail_not_subexponential (fun _ : ℕ => (1 : ℝ)) K rfl

end RH_HilbertLimit.FinitePrefix
