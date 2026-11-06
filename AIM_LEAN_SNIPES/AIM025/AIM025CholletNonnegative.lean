import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.LinearAlgebra.Matrix.Hadamard
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Field

set_option Elab.async true

/-!
# AIM025: the entrywise nonnegative permanent endpoint

This file formalizes the finite algebraic C1--C3 endpoint from
AIM025_CHOLLET_HVR_SUBCLASS_B_TIER.txt. The matrices have real,
entrywise nonnegative entries. Positive semidefiniteness is not assumed.

The native Mathlib Matrix.permanent is used throughout the matrix
conclusions. Its column-permutation definition is calibrated below to
the row-permutation weights used in the B-tier derivation.

No assertion about arbitrary complex Hermitian PSD matrices is made.
No local Lean execution or compiler pass is represented by this file.
-/

open scoped BigOperators

noncomputable section

namespace AIM025

section FiniteFamilies

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Total mass of a finite real family. -/
def mass (a : ι → ℝ) : ℝ := ∑ i, a i

/-- The contribution of pairs with the same index. -/
def diagonalPair (a b : ι → ℝ) : ℝ := ∑ i, a i * b i

/-- The contribution of ordered pairs with distinct indices. -/
def offDiagonalPair (a b : ι → ℝ) : ℝ :=
  ∑ i, ∑ j ∈ (Finset.univ : Finset ι).erase i, a i * b j

/-- The exact finite product expansion, with its diagonal separated. -/
theorem mass_mul_eq_diagonal_add_offDiagonal (a b : ι → ℝ) :
    mass a * mass b = diagonalPair a b + offDiagonalPair a b := by
  classical
  unfold mass diagonalPair offDiagonalPair
  calc
    (∑ i, a i) * (∑ j, b j) = ∑ i, ∑ j, a i * b j :=
      Fintype.sum_mul_sum a b
    _ = ∑ i, (a i * b i +
        ∑ j ∈ (Finset.univ : Finset ι).erase i, a i * b j) := by
      apply Finset.sum_congr rfl
      intro i hi
      calc
        (∑ j, a i * b j) =
            (∑ j ∈ (Finset.univ : Finset ι).erase i, a i * b j) + a i * b i :=
          (Finset.sum_erase_add Finset.univ (fun j => a i * b j)
            (Finset.mem_univ i)).symm
        _ = a i * b i +
            ∑ j ∈ (Finset.univ : Finset ι).erase i, a i * b j :=
          add_comm _ _
    _ = (∑ i, a i * b i) +
        ∑ i, ∑ j ∈ (Finset.univ : Finset ι).erase i, a i * b j :=
      Finset.sum_add_distrib

theorem mass_mul_sub_diagonal_eq_offDiagonal (a b : ι → ℝ) :
    mass a * mass b - diagonalPair a b = offDiagonalPair a b := by
  exact sub_eq_iff_eq_add.mpr
    ((mass_mul_eq_diagonal_add_offDiagonal a b).trans (add_comm _ _))

theorem mass_nonneg {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i) :
    0 ≤ mass a := by
  exact Finset.sum_nonneg (fun i _ => ha i)

theorem diagonalPair_nonneg {a b : ι → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) :
    0 ≤ diagonalPair a b := by
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (ha i) (hb i))

theorem offDiagonalPair_nonneg {a b : ι → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) :
    0 ≤ offDiagonalPair a b := by
  classical
  exact Finset.sum_nonneg (fun i _ =>
    Finset.sum_nonneg (fun j _ => mul_nonneg (ha i) (hb j)))

theorem diagonalPair_le_mass_mul {a b : ι → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) :
    diagonalPair a b ≤ mass a * mass b := by
  rw [mass_mul_eq_diagonal_add_offDiagonal]
  exact le_add_of_nonneg_right (offDiagonalPair_nonneg ha hb)

theorem mass_eq_zero_iff {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i) :
    mass a = 0 ↔ ∀ i, a i = 0 := by
  constructor
  · intro h i
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => ha j)).mp h
      i (Finset.mem_univ i)
  · intro h
    exact Finset.sum_eq_zero (fun i _ => h i)

theorem exists_pos_of_mass_ne_zero {a : ι → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hmass : mass a ≠ 0) :
    ∃ i, 0 < a i := by
  classical
  by_contra h
  apply hmass
  apply (mass_eq_zero_iff ha).mpr
  intro i
  apply le_antisymm
  · exact le_of_not_gt (fun hi => h ⟨i, hi⟩)
  · exact ha i

/-- No cancellation is possible between nonnegative off-diagonal terms. -/
theorem offDiagonalPair_eq_zero_iff {a b : ι → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) :
    offDiagonalPair a b = 0 ↔ ∀ i j, i ≠ j → a i * b j = 0 := by
  classical
  constructor
  · intro h i j hij
    have hi :
        (∑ k ∈ (Finset.univ : Finset ι).erase i, a i * b k) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun k _ => Finset.sum_nonneg
          (fun l _ => mul_nonneg (ha k) (hb l)))).mp h
            i (Finset.mem_univ i)
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun k _ => mul_nonneg (ha i) (hb k))).mp hi
        j (Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩)
  · intro h
    apply Finset.sum_eq_zero
    intro i hi
    apply Finset.sum_eq_zero
    intro j hj
    exact h i j (Ne.symm (Finset.ne_of_mem_erase hj))

/-- Each family has exactly the same single positive coordinate.
The other coordinates are explicitly zero. -/
def CommonUniquePositive (a b : ι → ℝ) : Prop :=
  ∃ i, 0 < a i ∧ 0 < b i ∧
    (∀ j, j ≠ i → a j = 0) ∧
    (∀ j, j ≠ i → b j = 0)

/-- Complete equality classification, including zero-mass cases. -/
theorem offDiagonalPair_eq_zero_iff_zero_or_commonUnique {a b : ι → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) :
    offDiagonalPair a b = 0 ↔
      mass a = 0 ∨ mass b = 0 ∨ CommonUniquePositive a b := by
  classical
  rw [offDiagonalPair_eq_zero_iff ha hb]
  constructor
  · intro hcross
    by_cases hA : mass a = 0
    · exact Or.inl hA
    by_cases hB : mass b = 0
    · exact Or.inr (Or.inl hB)
    obtain ⟨i, hai⟩ := exists_pos_of_mass_ne_zero ha hA
    obtain ⟨j, hbj⟩ := exists_pos_of_mass_ne_zero hb hB
    have hij : i = j := by
      by_contra hij
      exact (ne_of_gt (mul_pos hai hbj)) (hcross i j hij)
    subst j
    refine Or.inr (Or.inr ⟨i, hai, hbj, ?_, ?_⟩)
    · intro k hki
      exact (mul_eq_zero.mp (hcross k i hki)).resolve_right (ne_of_gt hbj)
    · intro k hki
      exact (mul_eq_zero.mp (hcross i k (Ne.symm hki))).resolve_left (ne_of_gt hai)
  · intro h
    rcases h with hA | hB | hsingle
    · intro i j hij
      rw [(mass_eq_zero_iff ha).mp hA i, zero_mul]
    · intro i j hij
      rw [(mass_eq_zero_iff hb).mp hB j, mul_zero]
    · rcases hsingle with ⟨i, hai, hbi, hA, hB⟩
      intro j k hjk
      by_cases hji : j = i
      · subst j
        rw [hB k (Ne.symm hjk), mul_zero]
      · rw [hA j hji, zero_mul]

/-- Normalization is a definition; the probability interpretation requires
nonzero mass, supplied explicitly in the corresponding theorems. -/
def normalized (a : ι → ℝ) (i : ι) : ℝ := a i / mass a

theorem normalized_nonneg {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i) :
    ∀ i, 0 ≤ normalized a i := by
  intro i
  exact div_nonneg (ha i) (mass_nonneg ha)

theorem mass_normalized {a : ι → ℝ} (ha : mass a ≠ 0) :
    mass (normalized a) = 1 := by
  change (∑ i, a i / mass a) = 1
  rw [← Finset.sum_div]
  exact div_self ha

/-- Algebraic overlap identity; it uses the field's total division.
Probability normalization is established separately by mass_normalized. -/
theorem normalized_overlap (a b : ι → ℝ) :
    diagonalPair (normalized a) (normalized b) =
      diagonalPair a b / (mass a * mass b) := by
  unfold diagonalPair normalized
  simp only [div_mul_div_comm]
  exact (Finset.sum_div Finset.univ (fun i => a i * b i)
    (mass a * mass b)).symm

theorem normalized_overlap_le_one {a b : ι → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (hA : mass a ≠ 0) (hB : mass b ≠ 0) :
    diagonalPair (normalized a) (normalized b) ≤ 1 := by
  have h := diagonalPair_le_mass_mul (normalized_nonneg ha) (normalized_nonneg hb)
  rw [mass_normalized hA, mass_normalized hB, mul_one] at h
  exact h

end FiniteFamilies

section Matrices

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Row-permutation weight, matching the B-tier mathematical definition. -/
def permTerm (A : Matrix n n ℝ) (σ : Equiv.Perm n) : ℝ :=
  ∏ i, A i (σ i)

/-- The row-permutation convention is exactly the native Mathlib permanent. -/
theorem permanent_eq_mass_permTerm (A : Matrix n n ℝ) :
    Matrix.permanent A = mass (permTerm A) := by
  calc
    Matrix.permanent A = Matrix.permanent (Matrix.transpose A) :=
      (Matrix.permanent_transpose A).symm
    _ = mass (permTerm A) := rfl

theorem permTerm_nonneg {A : Matrix n n ℝ}
    (hA : ∀ i j, 0 ≤ A i j) :
    ∀ σ, 0 ≤ permTerm A σ := by
  intro σ
  exact Finset.prod_nonneg (fun i _ => hA i (σ i))

theorem permanent_nonneg {A : Matrix n n ℝ}
    (hA : ∀ i j, 0 ≤ A i j) :
    0 ≤ Matrix.permanent A := by
  rw [permanent_eq_mass_permTerm]
  exact mass_nonneg (permTerm_nonneg hA)

theorem permTerm_hadamard (A B : Matrix n n ℝ) (σ : Equiv.Perm n) :
    permTerm (Matrix.hadamard A B) σ = permTerm A σ * permTerm B σ := by
  unfold permTerm
  simp only [Matrix.hadamard_apply, Finset.prod_mul_distrib]

theorem permanent_hadamard_eq_diagonalPair (A B : Matrix n n ℝ) :
    Matrix.permanent (Matrix.hadamard A B) = diagonalPair (permTerm A) (permTerm B) := by
  rw [permanent_eq_mass_permTerm]
  unfold mass diagonalPair
  apply Finset.sum_congr rfl
  intro σ hσ
  exact permTerm_hadamard A B σ

/-- The exact Chollet residual in native permanent notation. -/
def cholletGap (A B : Matrix n n ℝ) : ℝ :=
  Matrix.permanent A * Matrix.permanent B -
    Matrix.permanent (Matrix.hadamard A B)

/-- Exact residual identity: valid for arbitrary real entries. -/
theorem cholletGap_eq_offDiagonal (A B : Matrix n n ℝ) :
    cholletGap A B = offDiagonalPair (permTerm A) (permTerm B) := by
  unfold cholletGap
  rw [permanent_eq_mass_permTerm A, permanent_eq_mass_permTerm B,
    permanent_hadamard_eq_diagonalPair]
  exact mass_mul_sub_diagonal_eq_offDiagonal (permTerm A) (permTerm B)

theorem cholletGap_nonneg {A B : Matrix n n ℝ}
    (hA : ∀ i j, 0 ≤ A i j) (hB : ∀ i j, 0 ≤ B i j) :
    0 ≤ cholletGap A B := by
  rw [cholletGap_eq_offDiagonal]
  exact offDiagonalPair_nonneg (permTerm_nonneg hA) (permTerm_nonneg hB)

/-- C1: the original finite nonnegative-entry subclass, in every finite dimension. -/
theorem permanent_hadamard_le {A B : Matrix n n ℝ}
    (hA : ∀ i j, 0 ≤ A i j) (hB : ∀ i j, 0 ≤ B i j) :
    Matrix.permanent (Matrix.hadamard A B) ≤
      Matrix.permanent A * Matrix.permanent B := by
  exact sub_nonneg.mp (cholletGap_nonneg hA hB)

theorem cholletGap_eq_zero_iff_crossTerms {A B : Matrix n n ℝ}
    (hA : ∀ i j, 0 ≤ A i j) (hB : ∀ i j, 0 ≤ B i j) :
    cholletGap A B = 0 ↔
      ∀ σ τ : Equiv.Perm n, σ ≠ τ → permTerm A σ * permTerm B τ = 0 := by
  rw [cholletGap_eq_offDiagonal]
  exact offDiagonalPair_eq_zero_iff (permTerm_nonneg hA) (permTerm_nonneg hB)

/-- C3: all zero-permanent degeneracies are retained. -/
theorem cholletGap_eq_zero_iff {A B : Matrix n n ℝ}
    (hA : ∀ i j, 0 ≤ A i j) (hB : ∀ i j, 0 ≤ B i j) :
    cholletGap A B = 0 ↔
      Matrix.permanent A = 0 ∨ Matrix.permanent B = 0 ∨
        CommonUniquePositive (permTerm A) (permTerm B) := by
  rw [cholletGap_eq_offDiagonal,
    permanent_eq_mass_permTerm A, permanent_eq_mass_permTerm B]
  exact offDiagonalPair_eq_zero_iff_zero_or_commonUnique
    (permTerm_nonneg hA) (permTerm_nonneg hB)

/-- The same complete classification stated directly as equality of permanents. -/
theorem permanent_hadamard_eq_iff {A B : Matrix n n ℝ}
    (hA : ∀ i j, 0 ≤ A i j) (hB : ∀ i j, 0 ≤ B i j) :
    Matrix.permanent (Matrix.hadamard A B) =
        Matrix.permanent A * Matrix.permanent B ↔
      Matrix.permanent A = 0 ∨ Matrix.permanent B = 0 ∨
        CommonUniquePositive (permTerm A) (permTerm B) := by
  have hgap := cholletGap_eq_zero_iff hA hB
  unfold cholletGap at hgap
  rw [sub_eq_zero] at hgap
  exact Iff.trans eq_comm hgap

theorem cholletGap_eq_zero_iff_commonUnique {A B : Matrix n n ℝ}
    (hA : ∀ i j, 0 ≤ A i j) (hB : ∀ i j, 0 ≤ B i j)
    (hPA : 0 < Matrix.permanent A) (hPB : 0 < Matrix.permanent B) :
    cholletGap A B = 0 ↔ CommonUniquePositive (permTerm A) (permTerm B) := by
  rw [cholletGap_eq_zero_iff hA hB]
  simp only [ne_of_gt hPA, ne_of_gt hPB, false_or]

def permutationDistribution (A : Matrix n n ℝ) (σ : Equiv.Perm n) : ℝ :=
  permTerm A σ / Matrix.permanent A

theorem permutationDistribution_eq_normalized (A : Matrix n n ℝ) :
    permutationDistribution A = normalized (permTerm A) := by
  funext σ
  unfold permutationDistribution normalized
  rw [permanent_eq_mass_permTerm]

theorem permutationDistribution_nonneg {A : Matrix n n ℝ}
    (hA : ∀ i j, 0 ≤ A i j) :
    ∀ σ, 0 ≤ permutationDistribution A σ := by
  intro σ
  exact div_nonneg (permTerm_nonneg hA σ) (permanent_nonneg hA)

theorem permutationDistribution_sum (A : Matrix n n ℝ)
    (hA : 0 < Matrix.permanent A) :
    (∑ σ, permutationDistribution A σ) = 1 := by
  change mass (permutationDistribution A) = 1
  rw [permutationDistribution_eq_normalized]
  apply mass_normalized
  rw [← permanent_eq_mass_permTerm A]
  exact ne_of_gt hA

/-- C2 overlap identity, with the exact native permanent numerator. -/
theorem normalized_permanent_overlap (A B : Matrix n n ℝ) :
    Matrix.permanent (Matrix.hadamard A B) /
        (Matrix.permanent A * Matrix.permanent B) =
      diagonalPair (permutationDistribution A) (permutationDistribution B) := by
  rw [permutationDistribution_eq_normalized A,
    permutationDistribution_eq_normalized B, normalized_overlap,
    permanent_hadamard_eq_diagonalPair,
    permanent_eq_mass_permTerm A, permanent_eq_mass_permTerm B]

theorem normalized_cholletGap (A B : Matrix n n ℝ)
    (hA : 0 < Matrix.permanent A) (hB : 0 < Matrix.permanent B) :
    cholletGap A B / (Matrix.permanent A * Matrix.permanent B) =
      1 - diagonalPair (permutationDistribution A) (permutationDistribution B) := by
  unfold cholletGap
  rw [sub_div, div_self (mul_ne_zero (ne_of_gt hA) (ne_of_gt hB)),
    normalized_permanent_overlap]

theorem permutation_overlap_bounds {A B : Matrix n n ℝ}
    (hA : ∀ i j, 0 ≤ A i j) (hB : ∀ i j, 0 ≤ B i j)
    (hPA : 0 < Matrix.permanent A) (hPB : 0 < Matrix.permanent B) :
    0 ≤ diagonalPair (permutationDistribution A) (permutationDistribution B) ∧
      diagonalPair (permutationDistribution A) (permutationDistribution B) ≤ 1 := by
  constructor
  · exact diagonalPair_nonneg
      (permutationDistribution_nonneg hA) (permutationDistribution_nonneg hB)
  · have h := diagonalPair_le_mass_mul
        (permutationDistribution_nonneg hA) (permutationDistribution_nonneg hB)
    have hsumA : mass (permutationDistribution A) = 1 :=
      permutationDistribution_sum A hPA
    have hsumB : mass (permutationDistribution B) = 1 :=
      permutationDistribution_sum B hPB
    rw [hsumA, hsumB, mul_one] at h
    exact h

/-- On the positive-permanent branch, overlap one is exactly common singleton support. -/
theorem permutation_overlap_eq_one_iff {A B : Matrix n n ℝ}
    (hA : ∀ i j, 0 ≤ A i j) (hB : ∀ i j, 0 ≤ B i j)
    (hPA : 0 < Matrix.permanent A) (hPB : 0 < Matrix.permanent B) :
    diagonalPair (permutationDistribution A) (permutationDistribution B) = 1 ↔
      CommonUniquePositive (permTerm A) (permTerm B) := by
  rw [← cholletGap_eq_zero_iff_commonUnique hA hB hPA hPB]
  have hden : Matrix.permanent A * Matrix.permanent B ≠ 0 :=
    mul_ne_zero (ne_of_gt hPA) (ne_of_gt hPB)
  have hnorm := normalized_cholletGap A B hPA hPB
  constructor
  · intro h
    rw [h, sub_self] at hnorm
    have hgap := (div_eq_iff hden).mp hnorm
    simpa only [zero_mul] using hgap
  · intro h
    rw [h, zero_div] at hnorm
    exact (sub_eq_zero.mp hnorm.symm).symm

/-- Deterministic root composition of the independent finite-algebraic edges. -/
theorem AIM025_CHOLLET_NONNEGATIVE
    (A B : Matrix n n ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (hB : ∀ i j, 0 ≤ B i j) :
    cholletGap A B = offDiagonalPair (permTerm A) (permTerm B) ∧
    Matrix.permanent (Matrix.hadamard A B) ≤
      Matrix.permanent A * Matrix.permanent B ∧
    (cholletGap A B = 0 ↔
      Matrix.permanent A = 0 ∨ Matrix.permanent B = 0 ∨
        CommonUniquePositive (permTerm A) (permTerm B)) ∧
    (0 < Matrix.permanent A → 0 < Matrix.permanent B →
      (∑ σ, permutationDistribution A σ) = 1 ∧
      (∑ σ, permutationDistribution B σ) = 1 ∧
      Matrix.permanent (Matrix.hadamard A B) /
          (Matrix.permanent A * Matrix.permanent B) =
        diagonalPair (permutationDistribution A) (permutationDistribution B) ∧
      cholletGap A B / (Matrix.permanent A * Matrix.permanent B) =
        1 - diagonalPair (permutationDistribution A) (permutationDistribution B) ∧
      (0 ≤ diagonalPair (permutationDistribution A) (permutationDistribution B) ∧
        diagonalPair (permutationDistribution A) (permutationDistribution B) ≤ 1) ∧
      (diagonalPair (permutationDistribution A) (permutationDistribution B) = 1 ↔
        CommonUniquePositive (permTerm A) (permTerm B))) := by
  refine ⟨cholletGap_eq_offDiagonal A B, permanent_hadamard_le hA hB,
    cholletGap_eq_zero_iff hA hB, ?_⟩
  intro hPA hPB
  exact ⟨permutationDistribution_sum A hPA, permutationDistribution_sum B hPB,
    normalized_permanent_overlap A B, normalized_cholletGap A B hPA hPB,
    permutation_overlap_bounds hA hB hPA hPB,
    permutation_overlap_eq_one_iff hA hB hPA hPB⟩

end Matrices

section FinitePositiveGram

variable {n α β : Type*} [Fintype n] [DecidableEq n]
    [Fintype α] [Fintype β]

/-- Finite positive-measure Gram data. This is a finite specialization only;
no unbounded-operator or spectral-calculus premise is hidden in the definition. -/
def weightedGram (w : α → ℝ) (f : n → α → ℝ) : Matrix n n ℝ :=
  fun i j => ∑ k, w k * f i k * f j k

theorem weightedGram_entrywise_nonneg
    {w : α → ℝ} {f : n → α → ℝ}
    (hw : ∀ k, 0 ≤ w k) (hf : ∀ i k, 0 ≤ f i k) :
    ∀ i j, 0 ≤ weightedGram w f i j := by
  intro i j
  exact Finset.sum_nonneg
    (fun k _ => mul_nonneg (mul_nonneg (hw k) (hf i k)) (hf j k))

/-- The selected endpoint applies directly to finite positive Gram families. -/
theorem weightedGram_chollet
    {w : α → ℝ} {v : β → ℝ} {f : n → α → ℝ} {g : n → β → ℝ}
    (hw : ∀ k, 0 ≤ w k) (hv : ∀ k, 0 ≤ v k)
    (hf : ∀ i k, 0 ≤ f i k) (hg : ∀ i k, 0 ≤ g i k) :
    Matrix.permanent (Matrix.hadamard (weightedGram w f) (weightedGram v g)) ≤
      Matrix.permanent (weightedGram w f) * Matrix.permanent (weightedGram v g) := by
  exact permanent_hadamard_le
    (weightedGram_entrywise_nonneg hw hf) (weightedGram_entrywise_nonneg hv hg)

end FinitePositiveGram

end AIM025

