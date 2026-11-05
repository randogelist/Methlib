import Mathlib

open Filter Set Topology Polynomial
open scoped Polynomial ContDiff

noncomputable section

namespace CondGaussian

private def cutoff (s : ℝ) : ℝ := Real.smoothTransition (2 * s + 1)

private def extension (s : ℝ) : ℝ :=
  cutoff s * Real.exp (-s) / (1 + s * cutoff s)

private lemma denominator_pos (s : ℝ) : 0 < 1 + s * cutoff s := by
  by_cases h : 2 * s + 1 ≤ 0
  · simp [cutoff, Real.smoothTransition.zero_of_nonpos h]
  · have hs : -(1 / 2 : ℝ) < s := by linarith
    have hc := Real.smoothTransition.nonneg (2 * s + 1)
    have hc' := Real.smoothTransition.le_one (2 * s + 1)
    unfold cutoff
    by_cases hs' : 0 ≤ s
    · nlinarith [mul_nonneg hs' hc]
    · nlinarith [mul_nonneg (neg_nonneg.mpr (le_of_not_ge hs')) (sub_nonneg.mpr hc')]

private lemma extension_smooth : ContDiff ℝ ∞ extension := by
  have hc : ContDiff ℝ ∞ cutoff :=
    Real.smoothTransition.contDiff.comp (by fun_prop : ContDiff ℝ ∞ (fun s : ℝ => 2 * s + 1))
  exact (hc.mul (contDiff_id.neg.exp)).div
    (contDiff_const.add (contDiff_id.mul hc)) (fun s => (denominator_pos s).ne')

private lemma extension_pos {x : ℝ} (hx : 0 ≤ x) :
    extension x = Real.exp (-x) / (1 + x) := by
  simp [extension, cutoff, Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ 2 * x + 1)]

private lemma extension_neg {x : ℝ} (hx : x < -1) : extension x = 0 := by
  simp [extension, cutoff, Real.smoothTransition.zero_of_nonpos (by linarith : 2 * x + 1 ≤ 0)]

private def tailStep (p : ℝ[X]) : ℝ[X] := -p - X ^ 2 * p.derivative

private def tailPoly : ℕ → ℝ[X]
  | 0 => X
  | n + 1 => tailStep (tailPoly n)

private def evalTail (p : ℝ[X]) (s : ℝ) : ℝ :=
  Real.exp (-s) * p.eval ((1 + s)⁻¹)

private lemma tail_hasDerivAt (p : ℝ[X]) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (evalTail p) (evalTail (tailStep p) x) x := by
  have he : HasDerivAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-x)) x := by
    simpa using ((hasDerivAt_id x).neg.exp)
  have hd : HasDerivAt (fun s : ℝ => 1 + s) 1 x := by
    simpa using (hasDerivAt_id x).const_add 1
  have hu : HasDerivAt (fun s : ℝ => (1 + s)⁻¹) (-1 / (1 + x) ^ 2) x :=
    hd.inv (by dsimp; linarith)
  have hp := (p.hasDerivAt ((1 + x)⁻¹)).comp x hu
  have hvalue : evalTail (tailStep p) x =
      (-Real.exp (-x)) * p.eval ((1 + x)⁻¹) +
        Real.exp (-x) * (p.derivative.eval ((1 + x)⁻¹) * (-1 / (1 + x) ^ 2)) := by
    unfold evalTail tailStep
    rw [Polynomial.eval_sub, Polynomial.eval_neg, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_X, div_eq_mul_inv, ← inv_pow]
    ring
  rw [hvalue]
  exact he.mul hp

private lemma iteratedDeriv_pos (n : ℕ) (x : ℝ) (hx : 0 < x) :
    iteratedDeriv n extension x = evalTail (tailPoly n) x := by
  induction n generalizing x with
  | zero =>
    simp [extension_pos hx.le, tailPoly, evalTail, div_eq_mul_inv]
  | succ n ih =>
    have hloc : iteratedDeriv n extension =ᶠ[𝓝 x] evalTail (tailPoly n) := by
      filter_upwards [lt_mem_nhds hx] with y hy using ih y hy
    rw [iteratedDeriv_succ, hloc.deriv_eq]
    exact (tail_hasDerivAt (tailPoly n) hx).deriv

private lemma iteratedDeriv_neg_tail (n : ℕ) (x : ℝ) (hx : x < -1) :
    iteratedDeriv n extension x = 0 := by
  have hloc : extension =ᶠ[𝓝 x] (0 : ℝ → ℝ) := by
    filter_upwards [gt_mem_nhds hx] with y hy using extension_neg hy
  simpa using Filter.EventuallyEq.iteratedDeriv_eq n hloc

private lemma extension_decay (k n : ℕ) :
    ∃ C : ℝ, ∀ x : ℝ, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n extension x‖ ≤ C := by
  obtain ⟨R, hR⟩ := eventually_atTop.mp
    ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k).eventually_lt_const zero_lt_one)
  let T := max R 1
  obtain ⟨A, hA⟩ := (isCompact_Icc (α := ℝ) (a := 0) (b := 1)).exists_bound_of_continuousOn
    (f := fun y : ℝ => (tailPoly n).eval y) (tailPoly n).continuous.continuousOn
  let W := fun x : ℝ => ‖x‖ ^ k * ‖iteratedDeriv n extension x‖
  have hn : (n : ℕ∞ω) ≤ ∞ := by
    exact WithTop.coe_le_coe.mpr (le_top : (n : ℕ∞) ≤ ⊤)
  have hdn : Continuous (iteratedDeriv n extension) :=
    ContDiff.continuous_iteratedDeriv n extension_smooth hn
  have hW : Continuous W := (continuous_norm.pow k).mul hdn.norm
  obtain ⟨B, hB⟩ :=
    (isCompact_Icc (α := ℝ) (a := -1) (b := T)).exists_bound_of_continuousOn hW.continuousOn
  refine ⟨max 0 (max A B), fun x => ?_⟩
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  by_cases hx : x < -1
  · rw [iteratedDeriv_neg_tail n x hx, norm_zero, mul_zero]
    exact le_max_left _ _
  by_cases hT : x ≤ T
  · have hb := hB x ⟨le_of_not_gt hx, hT⟩
    simp only [Real.norm_of_nonneg (show 0 ≤ W x from mul_nonneg (pow_nonneg (norm_nonneg _) _) (norm_nonneg _))] at hb
    exact hb.trans ((le_max_right A B).trans (le_max_right _ _))
  have ht : T < x := lt_of_not_ge hT
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one ((le_max_right R 1).trans ht.le)
  have hsmall : x ^ k * Real.exp (-x) ≤ 1 := (hR x ((le_max_left R 1).trans ht.le)).le
  have harg : (1 + x)⁻¹ ∈ Icc (0 : ℝ) 1 :=
    ⟨inv_nonneg.mpr (by linarith), inv_le_one_of_one_le₀ (by linarith)⟩
  have hp := hA _ harg
  rw [iteratedDeriv_pos n x hxpos, evalTail, norm_mul, Real.norm_of_nonneg hxpos.le,
    Real.norm_of_nonneg (Real.exp_pos _).le, ← mul_assoc]
  calc
    _ ≤ 1 * ‖(tailPoly n).eval ((1 + x)⁻¹)‖ :=
      mul_le_mul_of_nonneg_right hsmall (norm_nonneg _)
    _ ≤ A := by simpa only [one_mul] using hp
    _ ≤ _ := (le_max_left A B).trans (le_max_right _ _)

/-- A real Schwartz extension of the exact radial scalar function on the
    nonnegative half-line. The extension across the negative half-line
    only provides a domain for Schwartz composition. -/
theorem exists_scalar_extension :
    ∃ G : SchwartzMap ℝ ℝ, ∀ s : ℝ, 0 ≤ s → G s = Real.exp (-s) / (1 + s) := by
  refine ⟨⟨extension, extension_smooth, extension_decay⟩, fun s hs => ?_⟩
  exact extension_pos hs

end CondGaussian
end

#print axioms CondGaussian.exists_scalar_extension
