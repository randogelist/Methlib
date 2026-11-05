import CondAmplitude

namespace CondFeffA

open MeasureTheory
open scoped BigOperators

/-- Uniform separation used to select N nodes from a finite-measure real set. -/
noncomputable def nodeSpacing (E : Set ℝ) (N : ℕ) : ℝ :=
  (volume E).toReal / (4 * ((N : ℝ) + 1))

/-- Positive Lebesgue measure supplies the radius in the finite packing argument. -/
theorem exists_positive_measure_nodes (E : Set ℝ) (N : ℕ)
    (hE : volume E ≠ 0) (hfin : volume E ≠ ⊤) :
    ∃ s : Finset ℝ, s.card = N ∧ (∀ x ∈ s, x ∈ E) ∧
      ∀ x ∈ s, ∀ y ∈ s, x ≠ y → nodeSpacing E N ≤ dist x y := by
  have hmass := ENNReal.toReal_pos hE hfin
  have hden : 0 < 4 * ((N : ℝ) + 1) := by positivity
  have hr : 0 < nodeSpacing E N := div_pos hmass hden
  apply exists_separated_nodes E N hr
  intro s hs
  have hcard : (s.card : ℝ) < (N : ℝ) := by exact_mod_cast hs
  have hs_nonneg : 0 ≤ (s.card : ℝ) := by positivity
  have hN_nonneg : 0 ≤ (N : ℝ) := by positivity
  have hsp : nodeSpacing E N * (4 * ((N : ℝ) + 1)) = (volume E).toReal :=
    div_mul_cancel₀ _ hden.ne'
  have hsmall : (s.card : ℝ) * (2 * nodeSpacing E N) < (volume E).toReal := by
    have hlen : 2 * (s.card : ℝ) < 4 * ((N : ℝ) + 1) := by
      linarith only [hcard, hN_nonneg]
    have hb := mul_lt_mul_of_pos_left hlen hr
    nlinarith only [hb, hsp]
  calc
    ∑ x ∈ s, volume (Metric.ball x (nodeSpacing E N)) =
        ENNReal.ofReal ((s.card : ℝ) * (2 * nodeSpacing E N)) := by
      simp only [Real.volume_ball, Finset.sum_const, nsmul_eq_mul,
        ENNReal.ofReal_mul hs_nonneg, ENNReal.ofReal_natCast]
    _ < volume E :=
      (ENNReal.ofReal_lt_iff_lt_toReal
        (mul_nonneg hs_nonneg (mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num) hr.le)) hfin).mpr hsmall

/-- Sorting turns pairwise separation into separation proportional to rank. -/
theorem rank_gap_of_separated {d : ℕ} {r : ℝ} (x : Fin (d + 1) ↪o ℝ)
    (hsep : ∀ i j, i ≠ j → r ≤ dist (x i) (x j)) :
    ∀ i j : Fin (d + 1), i ≤ j →
      r * ((j.val : ℝ) - (i.val : ℝ)) ≤ x j - x i := by
  have mono : Monotone (fun i : Fin (d + 1) => x i - r * (i.val : ℝ)) := by
    apply Fin.monotone_iff_le_succ.mpr
    intro k
    have hlt := x.strictMono k.castSucc_lt_succ
    have hdist := hsep k.succ k.castSucc k.castSucc_lt_succ.ne'
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hlt.le)] at hdist
    change x k.castSucc - r * (k.val : ℝ) ≤ x k.succ - r * ((k.val + 1 : ℕ) : ℝ)
    rw [Nat.cast_add, Nat.cast_one]
    linarith
  intro i j hij
  have hle := mono hij
  change x i - r * (i.val : ℝ) ≤ x j - r * (j.val : ℝ) at hle
  linarith

/-- Increasing nodes witnessing the denominator geometry in interpolation. -/
theorem exists_ranked_positive_measure_nodes (E : Set ℝ) (d : ℕ)
    (hE : volume E ≠ 0) (hfin : volume E ≠ ⊤) :
    ∃ x : Fin (d + 1) ↪o ℝ, (∀ i, x i ∈ E) ∧
      ∀ i j : Fin (d + 1), i ≤ j →
        nodeSpacing E (d + 1) * ((j.val : ℝ) - (i.val : ℝ)) ≤ x j - x i := by
  obtain ⟨s, hc, hmem, hsep⟩ := exists_positive_measure_nodes E (d + 1) hE hfin
  let x := s.orderEmbOfFin hc
  have hx (i : Fin (d + 1)) : x i ∈ s := s.orderEmbOfFin_mem hc i
  refine ⟨x, fun i => hmem _ (hx i), rank_gap_of_separated x ?_⟩
  intro i j hij
  exact hsep _ (hx i) _ (hx j) (x.injective.ne hij)

end CondFeffA

#print axioms CondFeffA.exists_positive_measure_nodes
#print axioms CondFeffA.rank_gap_of_separated
#print axioms CondFeffA.exists_ranked_positive_measure_nodes
