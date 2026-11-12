import SingularityDisprovement.DyadicArithmetic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Data.Complex.BigOperators

/-! Ordinary ordered convergence of the concrete dyadic cosine series.
The limit is an ordered partial-sum limit, not an unconditional `tsum`.
-/

set_option autoImplicit false
set_option Elab.async true

open Set Filter
open scoped BigOperators Topology

namespace SingularityDisprovement
noncomputable section

theorem dyadicAmplitude_tendsto_zero :
    Tendsto dyadicAmplitude atTop (𝓝 (0 : ℝ)) := by
  have hs := dyadicAmplitude_sq_summable.tendsto_atTop_zero
  have h := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  simpa only [Function.comp_def, Real.sqrt_sq (dyadicAmplitude_nonneg _),
    Real.sqrt_zero] using h

theorem dyadicAmplitude_shift_antitone :
    Antitone (fun n : ℕ => dyadicAmplitude (n + 2)) := by
  intro m n hmn
  exact dyadicAmplitude_antitone_from_two (by omega) (by omega)

theorem unit_geometric_partial_sum_bound (z : ℂ) (hz : ‖z‖ = 1)
    (hz1 : z ≠ 1) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, z ^ n‖ ≤ 2 / ‖z - 1‖ := by
  rw [geom_sum_eq hz1, norm_div]
  apply div_le_div_of_nonneg_right _ (norm_nonneg _)
  calc
    ‖z ^ N - 1‖ ≤ ‖z ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by simp [norm_pow, hz]

theorem unit_geometric_shift_partial_sum_bound (z : ℂ) (hz : ‖z‖ = 1)
    (hz1 : z ≠ 1) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, z ^ (n + 2)‖ ≤ 2 / ‖z - 1‖ := by
  simp_rw [pow_add]
  rw [← Finset.sum_mul, norm_mul, norm_pow, hz]
  simpa using unit_geometric_partial_sum_bound z hz hz1 N

theorem dyadicGeometric_exists_limit (z : ℂ) (hz : ‖z‖ = 1)
    (hz1 : z ≠ 1) :
    ∃ l : ℂ, Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.range N, dyadicAmplitude n • z ^ n)
      atTop (𝓝 l) := by
  have hzbound : ∀ N : ℕ,
      ‖∑ n ∈ Finset.range N, z ^ (n + 2)‖ ≤ 2 / ‖z - 1‖ :=
    unit_geometric_shift_partial_sum_bound z hz hz1
  have hd0 : Tendsto (fun n : ℕ => dyadicAmplitude (n + 2)) atTop (𝓝 (0 : ℝ)) :=
    (tendsto_add_atTop_iff_nat 2).mpr dyadicAmplitude_tendsto_zero
  have hc := dyadicAmplitude_shift_antitone.cauchySeq_series_mul_of_tendsto_zero_of_bounded
    hd0 hzbound
  obtain ⟨l, hl⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨l, (tendsto_add_atTop_iff_nat 2).mp ?_⟩
  have hshift (N : ℕ) :
      (∑ n ∈ Finset.range (N + 2), dyadicAmplitude n • z ^ n) =
        ∑ n ∈ Finset.range N, dyadicAmplitude (n + 2) • z ^ (n + 2) := by
    induction N with
    | zero => simp [Finset.sum_range_succ]
    | succ N ih =>
        simpa only [Nat.succ_add, Finset.sum_range_succ, ih]
  simpa only [hshift] using hl

def circlePhase (y : ℝ) : ℂ := Complex.exp (((2 * Real.pi * y : ℝ) : ℂ) * Complex.I)

theorem circlePhase_norm (y : ℝ) : ‖circlePhase y‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

theorem circlePhase_pow_re (y : ℝ) (n : ℕ) :
    ((circlePhase y) ^ n).re = Real.cos ((n : ℝ) * (2 * Real.pi * y)) := by
  unfold circlePhase
  rw [← Complex.exp_nat_mul]
  have h : (n : ℂ) * ((2 * Real.pi * y : ℝ) : ℂ) * Complex.I =
      (((n : ℝ) * (2 * Real.pi * y) : ℝ) : ℂ) * Complex.I := by
    push_cast
    rfl
  rw [← mul_assoc, h]
  exact Complex.exp_ofReal_mul_I_re _

theorem circlePhase_ne_one_of_not_int (y : ℝ)
    (hy : ∀ k : ℤ, y ≠ (k : ℝ)) : circlePhase y ≠ 1 := by
  intro heq
  obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp heq
  have him := congrArg Complex.im hk
  have heq' : (2 * Real.pi) * y = (2 * Real.pi) * (k : ℝ) := by
    simpa [Complex.mul_im, mul_assoc, mul_comm, mul_left_comm] using him
  exact hy k (mul_left_cancel₀ (by positivity : (2 : ℝ) * Real.pi ≠ 0) heq')

def dyadicCosinePartial (N : ℕ) (y : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N, dyadicAmplitude n * Real.cos ((n : ℝ) * (2 * Real.pi * y))

theorem dyadicCosine_exists_limit (y : ℝ)
    (hy : ∀ k : ℤ, y ≠ (k : ℝ)) :
    ∃ l : ℝ, Tendsto (fun N : ℕ => dyadicCosinePartial N y) atTop (𝓝 l) := by
  obtain ⟨l, hl⟩ := dyadicGeometric_exists_limit (circlePhase y)
    (circlePhase_norm y) (circlePhase_ne_one_of_not_int y hy)
  refine ⟨l.re, ?_⟩
  have h := Complex.continuous_re.continuousAt.tendsto.comp hl
  simpa only [Function.comp_def, Complex.re_sum, Complex.smul_re,
    smul_eq_mul, circlePhase_pow_re, dyadicCosinePartial] using h

/-- The actual ordinary cosine-series limit, completed arbitrarily on the null
set of integer arguments. -/
def dyadicCosineValue (y : ℝ) : ℝ :=
  if hy : ∀ k : ℤ, y ≠ (k : ℝ) then
    Classical.choose (dyadicCosine_exists_limit y hy)
  else 0

theorem dyadicCosine_tendsto (y : ℝ) (hy : ∀ k : ℤ, y ≠ (k : ℝ)) :
    Tendsto (fun N : ℕ => dyadicCosinePartial N y)
      atTop (𝓝 (dyadicCosineValue y)) := by
  rw [dyadicCosineValue, dif_pos hy]
  exact Classical.choose_spec (dyadicCosine_exists_limit y hy)

end
end SingularityDisprovement
