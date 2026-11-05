import CondNodes

namespace CondFeffA

open scoped BigOperators

/-- The missing diagonal in a product of distances contributes a factor of one. -/
private def indexWeight (i j : ℕ) : ℕ :=
  if j < i then i - j else if i < j then j - i else 1

private theorem indexWeight_self (i : ℕ) : indexWeight i i = 1 := by
  simp [indexWeight]

private theorem indexWeight_after (i j : ℕ) :
    indexWeight i (i + (j + 1)) = j + 1 := by
  have hlt : i < i + (j + 1) := by omega
  have hback : ¬ (i + (j + 1) < i) := not_lt_of_ge hlt.le
  rw [indexWeight, if_neg hback, if_pos hlt] <;> omega

private theorem indexWeight_product (d i : ℕ) (hi : i ≤ d) :
    (∏ j ∈ Finset.range (d + 1), indexWeight i j) =
      i.factorial * (d - i).factorial := by
  have left : (∏ j ∈ Finset.range i, indexWeight i j) = i.factorial := by
    calc
      (∏ j ∈ Finset.range i, indexWeight i j) =
          ∏ j ∈ Finset.range i, (i - 1 - j + 1) := by
        apply Finset.prod_congr rfl
        intro j hj
        have hj' : j < i := Finset.mem_range.mp hj
        rw [indexWeight, if_pos hj'] <;> omega
      _ = ∏ j ∈ Finset.range i, (j + 1) :=
        Finset.prod_range_reflect (fun j : ℕ => j + 1) i
      _ = i.factorial := Finset.prod_range_add_one_eq_factorial i
  have right (k : ℕ) : (∏ j ∈ Finset.range (k + 1), indexWeight i (i + j)) =
      k.factorial := by
    calc
      (∏ j ∈ Finset.range (k + 1), indexWeight i (i + j)) =
          (∏ j ∈ Finset.range k, indexWeight i (i + (j + 1))) *
            indexWeight i (i + 0) :=
        Finset.prod_range_succ' (fun j : ℕ => indexWeight i (i + j)) k
      _ = ∏ j ∈ Finset.range k, (j + 1) := by
        simp only [indexWeight_after, Nat.add_zero, indexWeight_self, mul_one]
      _ = k.factorial := Finset.prod_range_add_one_eq_factorial k
  have hlength : i + ((d - i) + 1) = d + 1 := by omega
  have splitProduct := Finset.prod_range_add (indexWeight i) i ((d - i) + 1)
  rw [hlength, left, right (d - i)] at splitProduct
  exact splitProduct

private theorem indexWeight_prod_erase {d : ℕ} (i : Fin (d+1)) :
    (∏ j ∈ Finset.univ.erase i, (indexWeight i.val j.val : ℝ)) =
      (i.val.factorial : ℝ) * ((d - i.val).factorial : ℝ) := by
  have hid : indexWeight i.val i.val = 1 := by simp [indexWeight]
  have hn : (∏ j ∈ Finset.univ.erase i, indexWeight i.val j.val) =
      i.val.factorial * (d-i.val).factorial := by
    calc
      (∏ j ∈ Finset.univ.erase i, indexWeight i.val j.val) =
          ∏ j : Fin (d+1), indexWeight i.val j.val := Finset.prod_erase _ hid
      _ = ∏ j ∈ Finset.range (d+1), indexWeight i.val j :=
        (Finset.prod_range (n := d + 1) (indexWeight i.val)).symm
      _ = _ := indexWeight_product _ _ (Nat.le_of_lt_succ i.isLt)
  rw [← Finset.prod_natCast, hn, Nat.cast_mul]

/-- Ordered spacing gives the factorial denominator of real Lagrange interpolation. -/
theorem ranked_denominator_lower {d : ℕ} {r : ℝ}
    (x : Fin (d+1) ↪o ℝ) (hr : 0 ≤ r)
    (hgap : ∀ i j : Fin (d+1), i ≤ j →
      r * ((j.val : ℝ) - (i.val : ℝ)) ≤ x j - x i) (i : Fin (d+1)) :
    r^d * (i.val.factorial : ℝ) * ((d-i.val).factorial : ℝ) ≤
      ∏ j ∈ Finset.univ.erase i, |x i-x j| := by
  have step (j : Fin (d+1)) (hj : j ∈ Finset.univ.erase i) :
      r * (indexWeight i.val j.val : ℝ) ≤ |x i - x j| := by
    have hne : j ≠ i := (Finset.mem_erase.mp hj).1
    rcases lt_or_gt_of_ne hne with hji | hij
    · have hval : j.val < i.val := hji
      have h := hgap j i hji.le
      rw [indexWeight, if_pos hval, Nat.cast_sub hval.le,
        abs_of_nonneg (sub_nonneg.mpr (x.monotone hji.le))]
      exact h
    · have hval : i.val < j.val := hij
      have h := hgap i j hij.le
      rw [indexWeight, if_neg (not_lt.mpr hval.le), if_pos hval,
        Nat.cast_sub hval.le, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (x.monotone hij.le))]
      exact h
  have hc : (Finset.univ.erase i).card = d := by simp
  calc
    r^d * (i.val.factorial : ℝ) * ((d-i.val).factorial : ℝ) =
        r^d * ∏ j ∈ Finset.univ.erase i, (indexWeight i.val j.val : ℝ) := by
      rw [indexWeight_prod_erase]; ring
    _ = ∏ j ∈ Finset.univ.erase i, r * (indexWeight i.val j.val : ℝ) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, hc]
    _ ≤ _ := Finset.prod_le_prod (fun j _ => mul_nonneg hr (Nat.cast_nonneg _)) step

/-- The same denominator expressed on the image finset used in scalar interpolation. -/
theorem ranked_denominator_image_lower {d : ℕ} {r : ℝ}
    (x : Fin (d+1) ↪o ℝ) (hr : 0 ≤ r)
    (hgap : ∀ i j : Fin (d+1), i ≤ j →
      r * ((j.val : ℝ) - (i.val : ℝ)) ≤ x j - x i) (i : Fin (d+1)) :
    r^d * (i.val.factorial : ℝ) * ((d-i.val).factorial : ℝ) ≤
      ∏ z ∈ (Finset.univ.image (fun k : Fin (d+1) => x k)).erase (x i), |x i-z| := by
  classical
  rw [← Finset.image_erase x.injective Finset.univ i, Finset.prod_image x.injective.injOn]
  exact ranked_denominator_lower x hr hgap i

end CondFeffA

#print axioms CondFeffA.ranked_denominator_lower
#print axioms CondFeffA.ranked_denominator_image_lower
