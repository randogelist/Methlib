import AIM939.Core
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
Diagonal concavity for the exact coefficient vector (1, 2, 3, 5, 1).

The polynomial curvature numerator is computed exactly. The fourth-root
derivatives are proved from Mathlib's real-power derivative theorem; the
concavity endpoint is obtained from the second-derivative criterion.

Prepared source only: no local Lean execution has been performed.
-/

noncomputable section

namespace AIM939

def diagonalPprime (t : ℝ) : ℝ := 8 + 36 * t + 60 * t ^ 2 + 4 * t ^ 3

def diagonalPsecond (t : ℝ) : ℝ := 36 + 120 * t + 12 * t ^ 2

def diagonalDefect (t : ℝ) : ℝ :=
  1 + 2 * t + 6 * t ^ 2 + 26 * t ^ 3 + 22 * t ^ 4

def diagonalFirst (t : ℝ) : ℝ :=
  diagonalPprime t * (1 / 4 : ℝ) * P t ^ (-3 / 4 : ℝ)

def diagonalSecond (t : ℝ) : ℝ :=
  (-3 : ℝ) * diagonalDefect t * P t ^ (-7 / 4 : ℝ)

theorem diagonal_P_pos {t : ℝ} (ht : 0 < t) : 0 < P t := by
  dsimp [P]
  positivity

theorem diagonal_defect_pos {t : ℝ} (ht : 0 < t) : 0 < diagonalDefect t := by
  dsimp [diagonalDefect]
  positivity

theorem diagonal_curvature_identity (t : ℝ) :
    4 * P t * diagonalPsecond t - 3 * (diagonalPprime t) ^ 2 =
      -48 * diagonalDefect t := by
  dsimp [P, diagonalPprime, diagonalPsecond, diagonalDefect]
  ring

theorem diagonal_hasDerivAt_P (t : ℝ) :
    HasDerivAt P (diagonalPprime t) t := by
  have hc : HasDerivAt (fun _ : ℝ => (1 : ℝ)) (0 : ℝ) t :=
    hasDerivAt_const t (1 : ℝ)
  have hx : HasDerivAt (fun s : ℝ => s) (1 : ℝ) t :=
    hasDerivAt_id' t
  have h2 : HasDerivAt (fun s : ℝ => s ^ 2) ((2 : ℝ) * t) t :=
    (hasDerivAt_pow 2 t).congr_deriv (by norm_num)
  have h3 : HasDerivAt (fun s : ℝ => s ^ 3) ((3 : ℝ) * t ^ 2) t :=
    (hasDerivAt_pow 3 t).congr_deriv (by norm_num)
  have h4 : HasDerivAt (fun s : ℝ => s ^ 4) ((4 : ℝ) * t ^ 3) t :=
    (hasDerivAt_pow 4 t).congr_deriv (by norm_num)
  have hraw :=
    ((((hc.add (hx.const_mul (8 : ℝ))).add (h2.const_mul (18 : ℝ))).add
      (h3.const_mul (20 : ℝ))).add h4)
  change HasDerivAt
    (fun s : ℝ => 1 + 8 * s + 18 * s ^ 2 + 20 * s ^ 3 + s ^ 4)
    ((0 : ℝ) + 8 * 1 + 18 * (2 * t) + 20 * (3 * t ^ 2) + 4 * t ^ 3) t at hraw
  have hvalue :
      (0 : ℝ) + 8 * 1 + 18 * (2 * t) + 20 * (3 * t ^ 2) + 4 * t ^ 3 =
        diagonalPprime t := by
    unfold diagonalPprime
    ring
  simpa only [P] using! hraw.congr_deriv hvalue

theorem diagonal_hasDerivAt_Pprime (t : ℝ) :
    HasDerivAt diagonalPprime (diagonalPsecond t) t := by
  have hc : HasDerivAt (fun _ : ℝ => (8 : ℝ)) (0 : ℝ) t :=
    hasDerivAt_const t (8 : ℝ)
  have hx : HasDerivAt (fun s : ℝ => s) (1 : ℝ) t :=
    hasDerivAt_id' t
  have h2 : HasDerivAt (fun s : ℝ => s ^ 2) ((2 : ℝ) * t) t :=
    (hasDerivAt_pow 2 t).congr_deriv (by norm_num)
  have h3 : HasDerivAt (fun s : ℝ => s ^ 3) ((3 : ℝ) * t ^ 2) t :=
    (hasDerivAt_pow 3 t).congr_deriv (by norm_num)
  have hraw :=
    (((hc.add (hx.const_mul (36 : ℝ))).add (h2.const_mul (60 : ℝ))).add
      (h3.const_mul (4 : ℝ)))
  change HasDerivAt
    (fun s : ℝ => 8 + 36 * s + 60 * s ^ 2 + 4 * s ^ 3)
    ((0 : ℝ) + 36 * 1 + 60 * (2 * t) + 4 * (3 * t ^ 2)) t at hraw
  have hvalue :
      (0 : ℝ) + 36 * 1 + 60 * (2 * t) + 4 * (3 * t ^ 2) =
        diagonalPsecond t := by
    unfold diagonalPsecond
    ring
  simpa only [diagonalPprime] using! hraw.congr_deriv hvalue

theorem diagonal_hasDerivAt_root {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => rootQuarter (P s)) (diagonalFirst t) t := by
  have hp : P t ≠ 0 := (diagonal_P_pos ht).ne'
  have hraw : HasDerivAt (fun s : ℝ => P s ^ (1 / 4 : ℝ))
      (diagonalPprime t * (1 / 4 : ℝ) * P t ^ ((1 / 4 : ℝ) - 1)) t :=
    (diagonal_hasDerivAt_P t).rpow_const
      (p := (1 / 4 : ℝ)) (Or.inl hp)
  have hvalue :
      diagonalPprime t * (1 / 4 : ℝ) * P t ^ ((1 / 4 : ℝ) - 1) =
        diagonalFirst t := by
    simp only [diagonalFirst,
      show (1 / 4 : ℝ) - 1 = (-3 / 4 : ℝ) by norm_num]
  simpa only [rootQuarter] using hraw.congr_deriv hvalue

theorem diagonal_hasDerivAt_first {t : ℝ} (ht : 0 < t) :
    HasDerivAt diagonalFirst (diagonalSecond t) t := by
  have hp : 0 < P t := diagonal_P_pos ht
  have hshift : P t ^ (-3 / 4 : ℝ) = P t * P t ^ (-7 / 4 : ℝ) := by
    calc
      P t ^ (-3 / 4 : ℝ) = P t ^ ((1 : ℝ) + (-7 / 4 : ℝ)) := by norm_num
      _ = P t ^ (1 : ℝ) * P t ^ (-7 / 4 : ℝ) :=
        Real.rpow_add hp (1 : ℝ) (-7 / 4 : ℝ)
      _ = P t * P t ^ (-7 / 4 : ℝ) := by rw [Real.rpow_one]
  have hscale : HasDerivAt
      (fun s : ℝ => diagonalPprime s * (1 / 4 : ℝ))
      (diagonalPsecond t * (1 / 4 : ℝ)) t :=
    (diagonal_hasDerivAt_Pprime t).mul_const (1 / 4 : ℝ)
  have hpowRaw : HasDerivAt (fun s : ℝ => P s ^ (-3 / 4 : ℝ))
      (diagonalPprime t * (-3 / 4 : ℝ) * P t ^ ((-3 / 4 : ℝ) - 1)) t :=
    (diagonal_hasDerivAt_P t).rpow_const
      (p := (-3 / 4 : ℝ)) (Or.inl hp.ne')
  have hpow : HasDerivAt (fun s : ℝ => P s ^ (-3 / 4 : ℝ))
      (diagonalPprime t * (-3 / 4 : ℝ) * P t ^ (-7 / 4 : ℝ)) t := by
    apply hpowRaw.congr_deriv
    rw [show (-3 / 4 : ℝ) - 1 = (-7 / 4 : ℝ) by norm_num]
  have hraw := hscale.mul hpow
  change HasDerivAt
      (fun s : ℝ => (diagonalPprime s * (1 / 4 : ℝ)) * P s ^ (-3 / 4 : ℝ))
      (diagonalPsecond t * (1 / 4 : ℝ) * P t ^ (-3 / 4 : ℝ) +
        (diagonalPprime t * (1 / 4 : ℝ)) *
          (diagonalPprime t * (-3 / 4 : ℝ) * P t ^ (-7 / 4 : ℝ))) t at hraw
  have hvalue :
      diagonalPsecond t * (1 / 4 : ℝ) * P t ^ (-3 / 4 : ℝ) +
        (diagonalPprime t * (1 / 4 : ℝ)) *
          (diagonalPprime t * (-3 / 4 : ℝ) * P t ^ (-7 / 4 : ℝ)) =
        diagonalSecond t := by
    rw [hshift]
    unfold diagonalSecond diagonalDefect diagonalPprime diagonalPsecond P
    ring
  simpa only [diagonalFirst] using! hraw.congr_deriv hvalue

theorem diagonal_second_nonpos {t : ℝ} (ht : 0 < t) : diagonalSecond t ≤ 0 := by
  have hd : 0 ≤ diagonalDefect t := (diagonal_defect_pos ht).le
  have hp : 0 ≤ P t ^ (-7 / 4 : ℝ) :=
    Real.rpow_nonneg (diagonal_P_pos ht).le (-7 / 4 : ℝ)
  dsimp [diagonalSecond]
  exact mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (by norm_num) hd) hp

theorem diagonal_concave :
    ConcaveOn ℝ (Set.Ioi (0 : ℝ)) (fun t => rootQuarter (P t)) := by
  have hf : ContinuousOn (fun t : ℝ => rootQuarter (P t)) (Set.Ioi (0 : ℝ)) := by
    intro t ht
    exact (diagonal_hasDerivAt_root (Set.mem_Ioi.mp ht)).continuousAt.continuousWithinAt
  refine concaveOn_of_hasDerivWithinAt2_nonpos
    (D := Set.Ioi (0 : ℝ))
    (f' := diagonalFirst) (f'' := diagonalSecond)
    (convex_Ioi (0 : ℝ)) hf ?_ ?_ ?_
  · intro t ht
    have ht' : 0 < t := Set.mem_Ioi.mp (interior_subset ht)
    exact (diagonal_hasDerivAt_root ht').hasDerivWithinAt
  · intro t ht
    have ht' : 0 < t := Set.mem_Ioi.mp (interior_subset ht)
    exact (diagonal_hasDerivAt_first ht').hasDerivWithinAt
  · intro t ht
    have ht' : 0 < t := Set.mem_Ioi.mp (interior_subset ht)
    exact diagonal_second_nonpos ht'

end AIM939
