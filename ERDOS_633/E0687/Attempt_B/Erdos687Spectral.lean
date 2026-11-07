import Mathlib

/-!
Finite-dimensional spectral certificate for prime-factor covering.
The arithmetic conclusions are exact for every positive modulus.
-/

namespace Erdos687Spectral

open scoped BigOperators

def survivorSet (q y : ℕ) (a : ℤ) : Finset ℕ :=
  (Finset.range y).filter (fun i => (a + (i : ℤ)).natAbs.Coprime q)

def survivorCount (q y : ℕ) (a : ℤ) : ℕ :=
  (survivorSet q y a).card

def Covered (q y : ℕ) (a : ℤ) : Prop :=
  ∀ i : ℕ, i < y → ¬ (a + (i : ℤ)).natAbs.Coprime q

theorem survivorCount_pos_iff (q y : ℕ) (a : ℤ) :
    0 < survivorCount q y a ↔
      ∃ i : ℕ, i < y ∧ (a + (i : ℤ)).natAbs.Coprime q := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ : (survivorSet q y a).Nonempty :=
      Finset.card_pos.mp h
    rcases Finset.mem_filter.mp hi with ⟨hir, hic⟩
    exact ⟨i, Finset.mem_range.mp hir, hic⟩
  · rintro ⟨i, hi, hc⟩
    apply Finset.card_pos.mpr
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi, hc⟩⟩

theorem survivorCount_zero_iff (q y : ℕ) (a : ℤ) :
    survivorCount q y a = 0 ↔ Covered q y a := by
  constructor
  · intro hz i hi hc
    have hp : 0 < survivorCount q y a :=
      (survivorCount_pos_iff q y a).2 ⟨i, hi, hc⟩
    omega
  · intro hc
    by_contra hn
    have hp : 0 < survivorCount q y a := Nat.pos_of_ne_zero hn
    obtain ⟨i, hi, hic⟩ := (survivorCount_pos_iff q y a).1 hp
    exact hc i hi hic

noncomputable def gramMatrix (q y : ℕ) (E : Finset ℤ) :
    Matrix (↥E) (↥E) ℝ := by
  classical
  exact Matrix.diagonal (fun t : ↥E => (survivorCount q y t.1 : ℝ))

noncomputable def gramDet (q y : ℕ) (E : Finset ℤ) : ℝ :=
  (gramMatrix q y E).det

theorem gramDet_eq_prod (q y : ℕ) (E : Finset ℤ) :
    gramDet q y E = ∏ t : ↥E, (survivorCount q y t.1 : ℝ) := by
  classical
  simp [gramDet, gramMatrix]

theorem gramForm_nonneg (q y : ℕ) (E : Finset ℤ)
    (v : ↥E → ℝ) :
    0 ≤ ∑ t : ↥E, (survivorCount q y t.1 : ℝ) * (v t) ^ 2 := by
  classical
  apply Finset.sum_nonneg
  intro t _
  exact mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)

theorem gramDet_pos_iff (q y : ℕ) (E : Finset ℤ) :
    0 < gramDet q y E ↔
      ∀ a : ℤ, a ∈ E → 0 < survivorCount q y a := by
  classical
  rw [gramDet_eq_prod]
  constructor
  · intro h a ha
    by_contra hn
    have hz : survivorCount q y a = 0 := Nat.eq_zero_of_not_pos hn
    let t : ↥E := ⟨a, ha⟩
    have hfac : (survivorCount q y t.1 : ℝ) = 0 := by
      exact_mod_cast hz
    have hzero : (∏ t : ↥E, (survivorCount q y t.1 : ℝ)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ t) hfac
    linarith
  · intro h
    apply Finset.prod_pos
    intro t _
    exact_mod_cast (h t.1 t.2)

theorem gramDet_zero_iff_covered (q y : ℕ) (E : Finset ℤ) :
    gramDet q y E = 0 ↔ ∃ a : ℤ, a ∈ E ∧ Covered q y a := by
  classical
  constructor
  · intro hz
    by_contra hn
    have hp : 0 < gramDet q y E := by
      apply (gramDet_pos_iff q y E).2
      intro a ha
      by_contra hc
      have hzero : survivorCount q y a = 0 :=
        Nat.eq_zero_of_not_pos hc
      exact hn ⟨a, ha, (survivorCount_zero_iff q y a).1 hzero⟩
    linarith
  · rintro ⟨a, ha, hc⟩
    have hz : survivorCount q y a = 0 :=
      (survivorCount_zero_iff q y a).2 hc
    rw [gramDet_eq_prod]
    apply Finset.prod_eq_zero (Finset.mem_univ (⟨a, ha⟩ : ↥E))
    simp [hz]

theorem survivorCount_mono (q : ℕ) (a : ℤ)
    {y z : ℕ} (hyz : y ≤ z) :
    survivorCount q y a ≤ survivorCount q z a := by
  unfold survivorCount
  apply Finset.card_le_card
  intro i hi
  obtain ⟨hir, hic⟩ := Finset.mem_filter.mp hi
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr
      (lt_of_lt_of_le (Finset.mem_range.mp hir) hyz), hic⟩

theorem gramDet_pos_propagates (q : ℕ) (E : Finset ℤ)
    {y z : ℕ} (hyz : y ≤ z) (h : 0 < gramDet q y E) :
    0 < gramDet q z E := by
  apply (gramDet_pos_iff q z E).2
  intro a ha
  exact lt_of_lt_of_le
    ((gramDet_pos_iff q y E).1 h a ha)
    (survivorCount_mono q a hyz)

end Erdos687Spectral
