import Mathlib

/-!
Exact four-variable instance of AIM939.
Native target: Lean 4.33.0 with the user's existing cached Mathlib.
Prepared source: external compilation and theorem-level audit are pending.
-/

noncomputable section

namespace AIM939

abbrev Point := Fin 4 → ℝ

def sigma1 (x : Point) : ℝ := x 0 + x 1 + x 2 + x 3

def sigma2 (x : Point) : ℝ :=
  x 0 * x 1 + x 0 * x 2 + x 0 * x 3 +
  x 1 * x 2 + x 1 * x 3 + x 2 * x 3

def sigma3 (x : Point) : ℝ :=
  x 0 * x 1 * x 2 + x 0 * x 1 * x 3 +
  x 0 * x 2 * x 3 + x 1 * x 2 * x 3

def sigma4 (x : Point) : ℝ := x 0 * x 1 * x 2 * x 3

/-- The elementary symmetric polynomials of orders zero through four. -/
def elementarySymmetric4 (k : Fin 5) (x : Point) : ℝ :=
  ![1, sigma1 x, sigma2 x, sigma3 x, sigma4 x] k

def coefficients : Fin 5 → ℝ := ![1, 2, 3, 5, 1]

def fOf (a : Fin 5 → ℝ) (x : Point) : ℝ :=
  ∑ k : Fin 5, a k * elementarySymmetric4 k x

def f (x : Point) : ℝ :=
  1 + 2 * sigma1 x + 3 * sigma2 x + 5 * sigma3 x + sigma4 x

def P (t : ℝ) : ℝ := 1 + 8 * t + 18 * t ^ 2 + 20 * t ^ 3 + t ^ 4

def rootQuarter (u : ℝ) : ℝ := u ^ (1 / 4 : ℝ)

def orthant : Set Point := {x | ∀ i, 0 < x i}

theorem coefficients_pos (k : Fin 5) : 0 < coefficients k := by
  fin_cases k <;> norm_num [coefficients]

theorem coefficients_nonneg (k : Fin 5) : 0 ≤ coefficients k :=
  le_of_lt (coefficients_pos k)

theorem fOf_coefficients (x : Point) : fOf coefficients x = f x := by
  norm_num [fOf, coefficients, elementarySymmetric4, Fin.sum_univ_succ, f] <;> ring

theorem f_diagonal (t : ℝ) : f (fun _ => t) = P t := by
  dsimp [f, sigma1, sigma2, sigma3, sigma4, P]
  ring

theorem f_pos {x : Point} (hx : x ∈ orthant) : 0 < f x := by
  have h0 : 0 < x 0 := hx 0
  have h1 : 0 < x 1 := hx 1
  have h2 : 0 < x 2 := hx 2
  have h3 : 0 < x 3 := hx 3
  dsimp [f, sigma1, sigma2, sigma3, sigma4]
  positivity

/-- The n=p=4 specialization of the original diagonal-concavity assertion. -/
def DiagonalConcavityAssertion4 : Prop :=
  ∀ a : Fin 5 → ℝ,
    (∀ k, 0 ≤ a k) →
    (∃ k, a k ≠ 0) →
    ConcaveOn ℝ (Set.Ioi (0 : ℝ))
      (fun t => rootQuarter (fOf a (fun _ => t))) →
    ConcaveOn ℝ orthant (fun x => rootQuarter (fOf a x))

end AIM939
