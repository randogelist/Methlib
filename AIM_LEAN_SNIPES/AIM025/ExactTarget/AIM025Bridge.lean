import AIM025CholletNonnegative
import AIM025Exact

set_option Elab.async true

/-!
# AIM025: transfer of the nonnegative-entry theorem to the exact domain

`CholletFor` uses native complex matrices, the native permanent, and the
real-axis partial order on `Complex`. The previously established real theorem
therefore gives a genuine special case of the original PSD conjecture after
complexification. The additional hypotheses that every entry is real and
nonnegative remain explicit throughout this file.

The final theorem assumes native `Matrix.PosSemidef` and proves both the
original inequality and nonnegativity of its real residual on this subclass.
It does not assert `CholletConjecture` or remove the entry restrictions.

STATUS = A_TIER_CANDIDATE.
EXTERNAL_COMPILER_AND_THEOREM_AXIOM_AUDIT = REQUIRED.
-/

open scoped BigOperators ComplexOrder

noncomputable section

namespace AIM025.Exact

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Entrywise application of the canonical ring homomorphism `ℝ →+* ℂ`. -/
def complexify (A : Matrix ι ι ℝ) : Matrix ι ι ℂ :=
  fun i j => (A i j : ℂ)

/-- The native permanent commutes with the canonical real embedding. -/
theorem permanent_complexify (A : Matrix ι ι ℝ) :
    Matrix.permanent (complexify A) = (Matrix.permanent A : ℂ) := by
  change
    (∑ σ : Equiv.Perm ι, ∏ i, Complex.ofRealHom (A (σ i) i)) =
      Complex.ofRealHom (∑ σ : Equiv.Perm ι, ∏ i, A (σ i) i)
  simp only [map_sum, map_prod]

/-- Complexification preserves the native entrywise product. -/
theorem complexify_hadamard (A B : Matrix ι ι ℝ) :
    complexify (Matrix.hadamard A B) =
      Matrix.hadamard (complexify A) (complexify B) := by
  funext i j
  change ((A i j * B i j : ℝ) : ℂ) = (A i j : ℂ) * (B i j : ℂ)
  exact Complex.ofReal_mul (A i j) (B i j)

/-- Zero imaginary parts identify a complex matrix with its real embedding. -/
theorem complexify_re_eq (A : Matrix ι ι ℂ)
    (hA : ∀ i j, (A i j).im = 0) :
    complexify (fun i j => (A i j).re) = A := by
  funext i j
  exact Complex.ext rfl (hA i j).symm

/-- The complex target restricts exactly to the real permanent inequality. -/
theorem cholletFor_complexify_iff (A B : Matrix ι ι ℝ) :
    CholletFor (complexify A) (complexify B) ↔
      Matrix.permanent (Matrix.hadamard A B) ≤
        Matrix.permanent A * Matrix.permanent B := by
  unfold CholletFor
  rw [← complexify_hadamard]
  simp only [permanent_complexify, ← Complex.ofReal_mul, Complex.real_le_real]

/-- The exact-domain residual agrees with the accepted real residual. -/
theorem cholletGap_complexify (A B : Matrix ι ι ℝ) :
    cholletGap (complexify A) (complexify B) =
      AIM025.cholletGap A B := by
  unfold cholletGap AIM025.cholletGap
  rw [← complexify_hadamard]
  simp only [permanent_complexify, Complex.ofReal_re]

/-- The accepted nonnegative real theorem transfers to the exact complex target. -/
theorem cholletFor_complexify_of_nonneg {A B : Matrix ι ι ℝ}
    (hA : ∀ i j, 0 ≤ A i j) (hB : ∀ i j, 0 ≤ B i j) :
    CholletFor (complexify A) (complexify B) := by
  exact (cholletFor_complexify_iff A B).mpr
    (AIM025.permanent_hadamard_le hA hB)

/-- Explicit real-entry and sign hypotheses; positive semidefiniteness is unnecessary. -/
theorem cholletFor_of_real_nonnegative_entries {A B : Matrix ι ι ℂ}
    (hAim : ∀ i j, (A i j).im = 0)
    (hBim : ∀ i j, (B i j).im = 0)
    (hAre : ∀ i j, 0 ≤ (A i j).re)
    (hBre : ∀ i j, 0 ≤ (B i j).re) :
    CholletFor A B := by
  have h :
      CholletFor (complexify (fun i j => (A i j).re))
        (complexify (fun i j => (B i j).re)) :=
    cholletFor_complexify_of_nonneg hAre hBre
  simpa only [complexify_re_eq A hAim, complexify_re_eq B hBim] using h

/-- In `ComplexOrder`, entrywise nonnegativity includes zero imaginary parts. -/
theorem cholletFor_of_entrywise_nonneg {A B : Matrix ι ι ℂ}
    (hA : ∀ i j, 0 ≤ A i j) (hB : ∀ i j, 0 ≤ B i j) :
    CholletFor A B := by
  exact cholletFor_of_real_nonnegative_entries
    (fun i j => ((Complex.nonneg_iff).mp (hA i j)).2.symm)
    (fun i j => ((Complex.nonneg_iff).mp (hB i j)).2.symm)
    (fun i j => ((Complex.nonneg_iff).mp (hA i j)).1)
    (fun i j => ((Complex.nonneg_iff).mp (hB i j)).1)

/-- A native-PSD special case of AIM025, retaining every extra entry hypothesis. -/
theorem AIM025_CHOLLET_PSD_REAL_NONNEGATIVE
    (A B : Matrix ι ι ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hAim : ∀ i j, (A i j).im = 0)
    (hBim : ∀ i j, (B i j).im = 0)
    (hAre : ∀ i j, 0 ≤ (A i j).re)
    (hBre : ∀ i j, 0 ≤ (B i j).re) :
    CholletFor A B ∧ 0 ≤ cholletGap A B := by
  have hChollet : CholletFor A B :=
    cholletFor_of_real_nonnegative_entries hAim hBim hAre hBre
  exact ⟨hChollet,
    (cholletFor_iff_gap_nonneg hA.isHermitian hB.isHermitian).mp hChollet⟩

end AIM025.Exact
