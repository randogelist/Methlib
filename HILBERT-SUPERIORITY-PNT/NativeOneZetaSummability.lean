import HVRNativeLSeriesNorm
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Tactic

/-!
Right-half-plane convergence by a p-series bound. The product identity groups
an absolutely convergent double series by the product of its indices. The
fiberwise regrouping follows Mathlib/NumberTheory/LSeries/Convolution.lean
(Michael Stoll, Apache 2.0).
-/

noncomputable section

namespace HVRNativeOneZetaSummability

open Complex LSeries

/-- A p-series dominates the Dirichlet series of any sequence bounded by one
on the positive integers. The term at zero vanishes by definition. -/
theorem summable_of_unit_bound {f : ℕ → ℂ} {s : ℂ}
    (hf : ∀ n ≠ 0, ‖f n‖ ≤ 1) (hs : 1 < s.re) :
    LSeriesSummable f s := by
  have hsum : Summable (fun n : ℕ => (n : ℝ) ^ (-s.re)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  change Summable (LSeries.term f s)
  refine hsum.of_norm_bounded ?_
  intro n
  rw [HVRNativeLSeriesNorm.norm_term]
  by_cases hn : n = 0
  · rw [if_pos hn]
    exact Real.rpow_nonneg (Nat.cast_nonneg n) _
  · rw [if_neg hn]
    calc
      ‖f n‖ / (n : ℝ) ^ s.re ≤ 1 / (n : ℝ) ^ s.re :=
        div_le_div_of_nonneg_right (hf n hn) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
      _ = (n : ℝ) ^ (-s.re) := by simp [Real.rpow_neg (Nat.cast_nonneg n), one_div]

/-- Multiply the two convergent series and group by the natural-number
product map. Zero indices are included in the fiber identity. -/
theorem convolution_sum {f g : ℕ → ℂ} {s : ℂ}
    (hf : LSeriesSummable f s) (hg : LSeriesSummable g s) :
    LSeries (LSeries.convolution f g) s = LSeries f s * LSeries g s := by
  have hf' : HasSum (LSeries.term f s) (LSeries f s) := hf.LSeriesHasSum
  have hg' : HasSum (LSeries.term g s) (LSeries g s) := hg.LSeriesHasSum
  have hcross := summable_mul_of_summable_norm hf'.summable.norm hg'.summable.norm
  have hsum : HasSum (LSeries.term (LSeries.convolution f g) s)
      (LSeries f s * LSeries g s) := by
    simpa only [LSeries.term_convolution'] using (hf'.mul hg' hcross).tsum_fiberwise
      (fun p : ℕ × ℕ => p.1 * p.2)
  exact hsum.tsum_eq

/-- Identify the constant-one series term by term with the half-plane
Dirichlet expansion of the actual zeta function. -/
theorem one_series_eq_zeta {s : ℂ} (hs : 1 < s.re) :
    LSeries (1 : ℕ → ℂ) s = riemannZeta s := by
  rw [zeta_eq_tsum_one_div_nat_cpow hs]
  unfold LSeries
  refine tsum_congr fun n => ?_
  exact LSeries.term_of_ne_zero' (ne_zero_of_one_lt_re hs) (1 : ℕ → ℂ) n

/-- The constant-one L-series converges absolutely on the half-plane. -/
theorem one_summable {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (1 : ℕ → ℂ) s := by
  apply summable_of_unit_bound ?_ hs
  intro n hn
  simp

/-- The arithmetic zeta L-series converges absolutely on the half-plane. -/
theorem arithmetic_zeta_summable {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n : ℕ => (ArithmeticFunction.zeta n : ℂ)) s := by
  apply summable_of_unit_bound ?_ hs
  intro n hn
  simp [ArithmeticFunction.zeta_apply_ne hn]

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
