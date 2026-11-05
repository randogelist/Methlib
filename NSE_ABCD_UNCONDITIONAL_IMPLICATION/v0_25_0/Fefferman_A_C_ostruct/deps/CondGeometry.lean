import CondRank
import CondLagrange
import CondWeight

namespace CondFeffA

open MeasureTheory
open scoped BigOperators Polynomial

/-- For a bounded positive-measure set, the reciprocals of the Lagrange
denominators on the ranked nodes have a common geometric bound. -/
private theorem ranked_nodes_reciprocal_bound (E : Set ℝ) (d : ℕ)
    (hd : 1 ≤ d) (hμ : 0 < (volume E).toReal)
    (x : Fin (d+1) ↪o ℝ)
    (hgap : ∀ i j : Fin (d+1), i ≤ j →
      nodeSpacing E (d+1) * ((j.val : ℝ) - (i.val : ℝ)) ≤ x j - x i)
    (B : ℕ)
    (hscale : ((d : ℝ) + 1) * (2 : ℝ)^d *
      (4 * ((d : ℝ) + 2) / (volume E).toReal)^d /
      (d.factorial : ℝ) ≤ (B : ℝ)^d) :
    let s := Finset.univ.image (fun k : Fin (d+1) => x k)
    (∑ y ∈ s, 1 / ∏ z ∈ s.erase y, |y-z|) ≤ (B : ℝ)^d := by
  classical
  let s := Finset.univ.image (fun k : Fin (d+1) => x k)
  change (∑ y ∈ s, 1 / ∏ z ∈ s.erase y, |y-z|) ≤ (B : ℝ)^d
  have hc : s.card = d + 1 := by
    simpa [s] using Finset.card_image_of_injective
      (Finset.univ : Finset (Fin (d+1))) x.injective
  let h := nodeSpacing E (d+1)
  have hform : h = (volume E).toReal / (4 * ((d : ℝ) + 2)) := by
    simp only [h, nodeSpacing, Nat.cast_add, Nat.cast_one]
    rw [show (d : ℝ) + 1 + 1 = (d : ℝ) + 2 by ring]
  have hpos : 0 < h := by rw [hform]; positivity
  have hfac : 0 < (d.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos d
  have hcst : 0 < h ^ d * (d.factorial : ℝ) := by positivity
  have hpoint (y : ℝ) (hy : y ∈ s) :
      1 / (∏ z ∈ s.erase y, |y-z|) ≤
        2^d / (h^d * (d.factorial : ℝ)) := by
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hy
    have hspl : (d.factorial : ℝ) ≤
        (2 : ℝ)^d * (i.val.factorial : ℝ) * ((d - i.val).factorial : ℝ) := by
      exact_mod_cast factorial_le_two_pow_mul_split d i.val (by omega)
    have hprod := ranked_denominator_image_lower x hpos.le hgap i
    change h^d * (i.val.factorial : ℝ) * ((d-i.val).factorial : ℝ) ≤
      ∏ z ∈ s.erase (x i), |x i-z| at hprod
    have hab : h^d * (d.factorial : ℝ) ≤
        2^d * ∏ z ∈ s.erase (x i), |x i-z| := by
      calc
        _ ≤ h^d * (2^d * (i.val.factorial : ℝ) * ((d-i.val).factorial : ℝ)) :=
          mul_le_mul_of_nonneg_left hspl (pow_nonneg hpos.le d)
        _ = 2^d * (h^d * (i.val.factorial : ℝ) * ((d-i.val).factorial : ℝ)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hprod (by positivity)
    have hp : 0 < ∏ z ∈ s.erase (x i), |x i-z| := by
      by_contra! hz
      have hneg := mul_nonpos_of_nonneg_of_nonpos (by positivity : 0 ≤ (2 : ℝ)^d) hz
      exact (not_lt_of_ge (hab.trans hneg)) hcst
    apply (div_le_div_iff₀ hp hcst).mpr
    simpa using hab
  calc
    (∑ y ∈ s, 1 / ∏ z ∈ s.erase y, |y-z|) ≤
        ∑ _y ∈ s, (2 : ℝ)^d / (h^d * (d.factorial : ℝ)) :=
          Finset.sum_le_sum hpoint
    _ = ((d : ℝ) + 1) * (2^d / (h^d * (d.factorial : ℝ))) := by
      simp only [Finset.sum_const, nsmul_eq_mul, hc, Nat.cast_add, Nat.cast_one]
    _ = ((d : ℝ) + 1) * 2^d *
          (4 * ((d : ℝ) + 2) / (volume E).toReal)^d / (d.factorial : ℝ) := by
      rw [hform]
      first
      | simpa [div_eq_mul_inv, mul_pow, mul_assoc, mul_left_comm, mul_comm]
      | field_simp [div_pow, hμ.ne', hfac.ne'] <;> ring
    _ ≤ _ := hscale

/-- No measure or interpolation assumption is needed for amplitude polynomials
whose degrees are at most n+1. -/
theorem interpolationNodeBound_of_degree {P : ℕ → ℝ[X]} {δ : ℝ} (hδ : 0 < δ)
    (hdeg : ∀ n, (P n).natDegree ≤ n+1) : InterpolationNodeBound P δ := by
  classical
  intro m hm
  let E := jetLevel P δ m
  have hE : E ⊆ Set.Ioo 0 δ := fun _ hx => hx.1
  have hfin : volume E ≠ ⊤ := by
    apply ne_of_lt
    apply (measure_mono hE).trans_lt
    simp [Real.volume_Ioo]
  have hμ := ENNReal.toReal_pos hm hfin
  obtain ⟨B, hB⟩ := reciprocal_weight_envelope hμ
  obtain ⟨K, hK⟩ := exists_nat_gt ((δ+1) * (B : ℝ))
  refine ⟨K, ?_⟩
  intro n
  let d := n+1
  have hd : 1 ≤ d := by dsimp [d]; omega
  obtain ⟨x, hx, hg⟩ := exists_ranked_positive_measure_nodes E d hm hfin
  let s := Finset.univ.image (fun i : Fin (d+1) => x i)
  have hc : s.card = d+1 := by
    simpa [s] using Finset.card_image_of_injective
      (Finset.univ : Finset (Fin (d+1))) x.injective
  have hmem (y : ℝ) (hy : y ∈ s) : y ∈ E := by
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hy
    exact hx i
  refine ⟨s, hmem, ?_, ?_⟩
  · apply (Polynomial.degree_le_natDegree).trans_lt
    exact_mod_cast (show (P n).natDegree < s.card from by
      rw [hc]; dsimp [d]; exact Nat.lt_succ_of_le (hdeg n))
  · have hradius (y : ℝ) (hy : y ∈ s) : |y| ≤ δ := by
      have hyI := hE (hmem y hy)
      simpa only [abs_of_pos hyI.1] using hyI.2.le
    have hsum := lagrange_linear_coeff_sum_of_reciprocal_distances s d δ (B : ℝ)
      hc hδ.le hradius (ranked_nodes_reciprocal_bound E d hd hμ x hg B (hB d hd))
    exact hsum.trans (pow_le_pow_left₀ (by positivity) hK.le d)

end CondFeffA

#print axioms CondFeffA.interpolationNodeBound_of_degree
