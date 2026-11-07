import RHShiftedHausdorff.EdgeBandExit

set_option autoImplicit false
noncomputable section

namespace RHShiftedHausdorff.NSEJoint

open RH_HilbertLimit
open RH_HilbertLimit.TwoRoutes

theorem bernsteinWeight_add
    (u v : ℕ → ℝ) (N j : ℕ) :
    bernsteinWeight (fun n => u n + v n) N j =
      bernsteinWeight u N j + bernsteinWeight v N j := by
  unfold bernsteinWeight
  calc
    (Nat.choose N j : ℝ) *
        ∑ r ∈ Finset.range (N - j + 1),
          (-1 : ℝ) ^ r * (Nat.choose (N - j) r : ℝ) *
            (u (j + r) + v (j + r)) =
      (Nat.choose N j : ℝ) *
        ∑ r ∈ Finset.range (N - j + 1),
          (((-1 : ℝ) ^ r * (Nat.choose (N - j) r : ℝ) * u (j + r)) +
           ((-1 : ℝ) ^ r * (Nat.choose (N - j) r : ℝ) * v (j + r))) := by
        congr 1
        apply Finset.sum_congr rfl
        intro r hr
        ring
    _ =
      (Nat.choose N j : ℝ) *
          ((∑ r ∈ Finset.range (N - j + 1),
              (-1 : ℝ) ^ r * (Nat.choose (N - j) r : ℝ) * u (j + r)) +
           (∑ r ∈ Finset.range (N - j + 1),
              (-1 : ℝ) ^ r * (Nat.choose (N - j) r : ℝ) * v (j + r))) := by
        rw [Finset.sum_add_distrib]
    _ = _ := by ring

theorem bernsteinWeight_smul
    (a : ℝ) (u : ℕ → ℝ) (N j : ℕ) :
    bernsteinWeight (fun n => a * u n) N j =
      a * bernsteinWeight u N j := by
  unfold bernsteinWeight
  calc
    (Nat.choose N j : ℝ) *
        ∑ r ∈ Finset.range (N - j + 1),
          (-1 : ℝ) ^ r * (Nat.choose (N - j) r : ℝ) * (a * u (j + r)) =
      (Nat.choose N j : ℝ) *
        ∑ r ∈ Finset.range (N - j + 1),
          a * ((-1 : ℝ) ^ r * (Nat.choose (N - j) r : ℝ) * u (j + r)) := by
        congr 1
        apply Finset.sum_congr rfl
        intro r hr
        ring
    _ =
      (Nat.choose N j : ℝ) *
        (a * ∑ r ∈ Finset.range (N - j + 1),
          (-1 : ℝ) ^ r * (Nat.choose (N - j) r : ℝ) * u (j + r)) := by
        apply congrArg (fun x : ℝ => (Nat.choose N j : ℝ) * x)
        exact (Finset.mul_sum
          (Finset.range (N - j + 1))
          (fun r =>
            (-1 : ℝ) ^ r * (Nat.choose (N - j) r : ℝ) * u (j + r))
          a).symm
    _ = _ := by ring

theorem bernsteinPositive_zero :
    BernsteinPositive (fun _ : ℕ => (0 : ℝ)) := by
  intro N j hj
  simp [bernsteinWeight]

theorem bernsteinPositive_add
    {u v : ℕ → ℝ}
    (hu : BernsteinPositive u)
    (hv : BernsteinPositive v) :
    BernsteinPositive (fun n => u n + v n) := by
  intro N j hj
  rw [bernsteinWeight_add]
  exact add_nonneg (hu N j hj) (hv N j hj)

theorem bernsteinPositive_smul
    {u : ℕ → ℝ} {a : ℝ}
    (ha : 0 ≤ a)
    (hu : BernsteinPositive u) :
    BernsteinPositive (fun n => a * u n) := by
  intro N j hj
  rw [bernsteinWeight_smul]
  exact mul_nonneg ha (hu N j hj)

end RHShiftedHausdorff.NSEJoint
