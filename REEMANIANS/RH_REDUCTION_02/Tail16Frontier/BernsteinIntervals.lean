import Tail16Frontier.MomentData
import RH_HilbertLimit.Cancellation
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open scoped BigOperators

namespace Tail16Frontier

/-- Exact rational Bernstein evaluation of the supplied center coordinates. -/
def qBernstein (d : MomentData) (N j : Nat) : ℚ :=
  (Nat.choose N j : ℚ) *
    ∑ r ∈ Finset.range (N - j + 1),
      (-1 : ℚ)^r * (Nat.choose (N-j) r : ℚ) * d.center (j+r)

/-- Entrywise error obtained by the finite triangle inequality. -/
def entryError (d : MomentData) (N j : Nat) : ℚ :=
  (Nat.choose N j : ℚ) *
    ∑ r ∈ Finset.range (N-j+1),
      (Nat.choose (N-j) r : ℚ) * d.radius (j+r)

def qVariation (d : MomentData) (N : Nat) : ℚ :=
  ∑ j ∈ Finset.range (N+1), |qBernstein d N j|

/-- Sum-of-entry-errors form; no unproved reindexing identity is needed. -/
def rowError (d : MomentData) (N : Nat) : ℚ :=
  ∑ j ∈ Finset.range (N+1), entryError d N j

private theorem abs_sum_le_of_bounds
    (s : Finset Nat) (f g : Nat → ℝ)
    (h : ∀ i ∈ s, |f i| ≤ g i) :
    |∑ i ∈ s, f i| ≤ ∑ i ∈ s, g i := by
  revert h
  induction s using Finset.induction_on with
  | empty =>
      intro h
      simp
  | @insert i s hi ih =>
      intro h
      have hhead : |f i| ≤ g i := h i (by simp)
      have htail : ∀ j ∈ s, |f j| ≤ g j := by
        intro j hj
        exact h j (by simp [hj])
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      exact (abs_add_le _ _).trans (add_le_add hhead (ih htail))

private theorem abs_abs_sub_bound (x y : ℝ) :
    abs (abs x - abs y) ≤ abs (x - y) := by
  have hxy : |x| ≤ |x-y| + |y| := by
    calc
      |x| = |(x-y)+y| := by congr 1 <;> ring
      _ ≤ |x-y|+|y| := abs_add_le _ _
  have hyx : |y| ≤ |x-y| + |x| := by
    calc
      |y| = |(y-x)+x| := by congr 1 <;> ring
      _ ≤ |y-x|+|x| := abs_add_le _ _
      _ = |x-y|+|x| := by rw [abs_sub_comm y x]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

@[simp] theorem qBernstein_cast (d : MomentData) (N j : Nat) :
    (qBernstein d N j : ℝ) =
      RH_HilbertLimit.bernsteinWeight
        (fun k => (d.center k : ℝ)) N j := by
  unfold qBernstein RH_HilbertLimit.bernsteinWeight
  push_cast <;> rfl

@[simp] theorem entryError_cast (d : MomentData) (N j : Nat) :
    (entryError d N j : ℝ) =
      (Nat.choose N j : ℝ) *
        ∑ r ∈ Finset.range (N-j+1),
          (Nat.choose (N-j) r : ℝ) * (d.radius (j+r) : ℝ) := by
  unfold entryError
  push_cast <;> rfl

private theorem rat_abs_cast (q : ℚ) : ((|q| : ℚ) : ℝ) = |(q : ℝ)| := by
  by_cases hq : 0 ≤ q
  · have hqR : (0 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    rw [abs_of_nonneg hq, abs_of_nonneg hqR]
  · have hq' : q ≤ 0 := le_of_not_ge hq
    have hqR : (q : ℝ) ≤ 0 := by exact_mod_cast hq'
    rw [abs_of_nonpos hq', abs_of_nonpos hqR]
    push_cast <;> rfl

@[simp] theorem qVariation_cast (d : MomentData) (N : Nat) :
    (qVariation d N : ℝ) =
      ∑ j ∈ Finset.range (N+1), |(qBernstein d N j : ℝ)| := by
  unfold qVariation
  push_cast <;> simp only [rat_abs_cast]

@[simp] theorem rowError_cast (d : MomentData) (N : Nat) :
    (rowError d N : ℝ) =
      ∑ j ∈ Finset.range (N+1), (entryError d N j : ℝ) := by
  unfold rowError
  push_cast <;> rfl

private theorem bernstein_difference (u v : Nat → ℝ) (N j : Nat) :
    RH_HilbertLimit.bernsteinWeight u N j -
      RH_HilbertLimit.bernsteinWeight v N j =
    (Nat.choose N j : ℝ) *
      ∑ r ∈ Finset.range (N-j+1),
        (-1 : ℝ)^r * (Nat.choose (N-j) r : ℝ) * (u (j+r)-v (j+r)) := by
  unfold RH_HilbertLimit.bernsteinWeight
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  ring

/-- Entrywise actual meaning remains an explicit, kernel-checked premise. -/
theorem entry_error_bound (d : MomentData) (N j : Nat)
    (hdata : d.Encloses N) (hj : j ≤ N) :
    |RH_HilbertLimit.bernsteinWeight
        RH_HilbertLimit.actualNormalizedMoment N j -
      (qBernstein d N j : ℝ)| ≤ (entryError d N j : ℝ) := by
  rw [qBernstein_cast, bernstein_difference, entryError_cast]
  have hchoose : (0 : ℝ) ≤ (Nat.choose N j : ℝ) := Nat.cast_nonneg _
  rw [abs_mul, abs_of_nonneg hchoose]
  apply mul_le_mul_of_nonneg_left _ hchoose
  apply abs_sum_le_of_bounds
  intro r hr
  have hrN : j+r ≤ N := by
    have hr' := Finset.mem_range.mp hr
    omega
  have hpoint := hdata (j+r) hrN
  have hc : (0 : ℝ) ≤ (Nat.choose (N-j) r : ℝ) := Nat.cast_nonneg _
  calc
    |(-1 : ℝ)^r * (Nat.choose (N-j) r : ℝ) *
        (RH_HilbertLimit.actualNormalizedMoment (j+r) -
          (d.center (j+r) : ℝ))| =
      (Nat.choose (N-j) r : ℝ) *
        |RH_HilbertLimit.actualNormalizedMoment (j+r) -
          (d.center (j+r) : ℝ)| := by
            simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow,
              one_mul, abs_of_nonneg hc]
    _ ≤ (Nat.choose (N-j) r : ℝ) * (d.radius (j+r) : ℝ) :=
      mul_le_mul_of_nonneg_left hpoint hc

/-- The finite row-variation error is bounded by the sum of entry errors. -/
theorem variation_error_bound (d : MomentData) (N : Nat)
    (hdata : d.Encloses N) :
    |RH_HilbertLimit.actualVariation N - (qVariation d N : ℝ)|
      ≤ (rowError d N : ℝ) := by
  rw [qVariation_cast, rowError_cast]
  change |(∑ j ∈ Finset.range (N+1),
      |RH_HilbertLimit.bernsteinWeight
        RH_HilbertLimit.actualNormalizedMoment N j|) -
    (∑ j ∈ Finset.range (N+1), |(qBernstein d N j : ℝ)|)| ≤ _
  rw [← Finset.sum_sub_distrib]
  apply abs_sum_le_of_bounds
  intro j hj
  have hjN : j ≤ N := by
    have := Finset.mem_range.mp hj
    omega
  exact (abs_abs_sub_bound _ _).trans (entry_error_bound d N j hdata hjN)

end Tail16Frontier

