import Mathlib.Algebra.Star.BigOperators
import Mathlib.Analysis.Complex.Order
import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.LinearAlgebra.Matrix.PosDef

set_option Elab.async true

/-!
# AIM025: exact complex Hermitian positive-semidefinite target

Target source:
`MColbrook/AIM`, commit `4f5b1659355cb61d194da94ef14615214e1363a8`,
`problems/025-chollet-permanent.md`.

Dependency source:
mathlib commit `db584cd6d46c92f209a44c0f1c829460d327499d`;
native external Lean 4.33.0.

STATUS: A_TIER_CANDIDATE. No local Lean execution. Promotion requires a
matching external compiler result and theorem-level axiom audit.

`CholletConjecture` is the exact unresolved universal proposition.
No declaration in this file proves that proposition without a premise.
The theorem declarations specify its semantics, its residual equivalence,
and the necessary and sufficient form of a counterexample.

The complex order in `ComplexOrder` is the canonical partial order:
`z <= w` iff `z.re <= w.re` and `z.im = w.im`. Hermitian-permanent
reality below proves that its use in `CholletFor` is exactly the ordinary
real comparison required by the original statement.
-/

open scoped BigOperators ComplexOrder

noncomputable section

namespace AIM025.Exact

section FiniteIndex

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Conjugate transposition commutes with the permanent via scalar star. -/
theorem permanent_conjTranspose (A : Matrix ι ι ℂ) :
    Matrix.permanent (Matrix.conjTranspose A) = star (Matrix.permanent A) := by
  calc
    Matrix.permanent (Matrix.conjTranspose A) =
        star (Matrix.permanent (Matrix.transpose A)) := by
      simp only [Matrix.permanent, Matrix.conjTranspose, Matrix.map_apply,
        star_sum, star_prod]
    _ = star (Matrix.permanent A) := by
      rw [Matrix.permanent_transpose]

/-- A Hermitian matrix has a self-adjoint scalar permanent. -/
theorem permanent_star_eq_of_isHermitian {A : Matrix ι ι ℂ}
    (hA : A.IsHermitian) :
    star (Matrix.permanent A) = Matrix.permanent A := by
  rw [← permanent_conjTranspose, hA.eq]

/-- The permanent of a complex Hermitian matrix is real. -/
theorem permanent_im_eq_zero {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    (Matrix.permanent A).im = 0 := by
  apply Complex.conj_eq_iff_im.mp
  simpa only [Complex.star_def] using permanent_star_eq_of_isHermitian hA

/-- The real part retains the complete permanent on Hermitian inputs. -/
theorem permanent_eq_ofReal_re {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    Matrix.permanent A = ((Matrix.permanent A).re : ℂ) := by
  apply Complex.ext
  · rfl
  · simpa only [Complex.ofReal_im] using permanent_im_eq_zero hA

/-- The permanent of the Hadamard product of Hermitian matrices is real. -/
theorem permanent_hadamard_im_eq_zero {A B : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (Matrix.permanent (Matrix.hadamard A B)).im = 0 :=
  permanent_im_eq_zero (hA.hadamard hB)

/-- The original, unnormalised permanent comparison for a fixed pair. -/
def CholletFor (A B : Matrix ι ι ℂ) : Prop :=
  Matrix.permanent (Matrix.hadamard A B) ≤
    Matrix.permanent A * Matrix.permanent B

/-- Native complex order reduces exactly to the real permanent comparison. -/
theorem cholletFor_iff_re {A B : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    CholletFor A B ↔
      (Matrix.permanent (Matrix.hadamard A B)).re ≤
        (Matrix.permanent A).re * (Matrix.permanent B).re := by
  simp [CholletFor, Complex.le_def, Complex.mul_re, Complex.mul_im,
    permanent_im_eq_zero hA, permanent_im_eq_zero hB,
    permanent_hadamard_im_eq_zero hA hB]

/-- Exact real residual; nonnegativity is not assumed in this definition. -/
def cholletGap (A B : Matrix ι ι ℂ) : ℝ :=
  (Matrix.permanent A).re * (Matrix.permanent B).re -
    (Matrix.permanent (Matrix.hadamard A B)).re

/-- Residual nonnegativity is equivalent to the target on Hermitian pairs. -/
theorem cholletFor_iff_gap_nonneg {A B : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    CholletFor A B ↔ 0 ≤ cholletGap A B := by
  unfold cholletGap
  rw [sub_nonneg]
  exact cholletFor_iff_re hA hB

/-- A negative residual is exactly a failure of the Hermitian comparison. -/
theorem not_cholletFor_iff_gap_neg {A B : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    ¬ CholletFor A B ↔ cholletGap A B < 0 := by
  rw [cholletFor_iff_gap_nonneg hA hB, not_le]

end FiniteIndex

/-- AIM025 at the specified finite dimension, with native PSD hypotheses. -/
def CholletAt (n : ℕ) : Prop :=
  ∀ A B : Matrix (Fin n) (Fin n) ℂ,
    A.PosSemidef → B.PosSemidef → CholletFor A B

/--
The exact AIM025 universal target. This proposition remains unresolved.
The quantifier excludes the empty dimension and imposes no entrywise sign,
reality, normalisation, rank, or factorisation restriction.
-/
def CholletConjecture : Prop :=
  ∀ n : ℕ, 1 ≤ n → CholletAt n

/--
The exact remaining universal residual obligation. This definition does
not supply a certificate or a proof of that obligation.
-/
def PSDResidualNonnegative : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    ∀ A B : Matrix (Fin n) (Fin n) ℂ,
      A.PosSemidef → B.PosSemidef → 0 ≤ cholletGap A B

/-- Exact residual formulation at each fixed dimension. -/
theorem cholletAt_iff_gap_nonneg (n : ℕ) :
    CholletAt n ↔
      ∀ A B : Matrix (Fin n) (Fin n) ℂ,
        A.PosSemidef → B.PosSemidef → 0 ≤ cholletGap A B := by
  constructor
  · intro h A B hA hB
    exact (cholletFor_iff_gap_nonneg hA.isHermitian hB.isHermitian).mp
      (h A B hA hB)
  · intro h A B hA hB
    exact (cholletFor_iff_gap_nonneg hA.isHermitian hB.isHermitian).mpr
      (h A B hA hB)

/-- Exact equivalence; neither unresolved universal side is asserted. -/
theorem cholletConjecture_iff_residual_nonnegative :
    CholletConjecture ↔ PSDResidualNonnegative := by
  constructor
  · intro h n hn
    exact (cholletAt_iff_gap_nonneg n).mp (h n hn)
  · intro h n hn
    exact (cholletAt_iff_gap_nonneg n).mpr (h n hn)

/-- A genuine AIM025 counterexample includes both native PSD witnesses. -/
def Counterexample : Prop :=
  ∃ n : ℕ, 1 ≤ n ∧
    ∃ A B : Matrix (Fin n) (Fin n) ℂ,
      A.PosSemidef ∧ B.PosSemidef ∧ cholletGap A B < 0

/-- Any PSD pair with a strictly negative exact residual refutes AIM025. -/
theorem negative_gap_refutes_CholletConjecture {n : ℕ} (hn : 1 ≤ n)
    {A B : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hgap : cholletGap A B < 0) : ¬ CholletConjecture := by
  intro h
  have hnonneg : 0 ≤ cholletGap A B :=
    (cholletFor_iff_gap_nonneg hA.isHermitian hB.isHermitian).mp
      (h n hn A B hA hB)
  exact (not_lt_of_ge hnonneg) hgap

/-- Classical failure of the universal statement is exactly such a witness. -/
theorem not_cholletConjecture_iff_counterexample :
    ¬ CholletConjecture ↔ Counterexample := by
  classical
  constructor
  · intro hnot
    by_contra hcounterexample
    apply hnot
    intro n hn A B hA hB
    apply (cholletFor_iff_gap_nonneg hA.isHermitian hB.isHermitian).mpr
    by_contra hgap
    exact hcounterexample ⟨n, hn, A, B, hA, hB, lt_of_not_ge hgap⟩
  · rintro ⟨n, hn, A, B, hA, hB, hgap⟩
    exact negative_gap_refutes_CholletConjecture hn hA hB hgap

end AIM025.Exact
