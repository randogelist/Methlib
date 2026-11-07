import RHShiftedHausdorff.NSEJoint.BernsteinCone
import Mathlib.Analysis.SpecialFunctions.Exp

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace RHShiftedHausdorff.NSEJoint

open RH_HilbertLimit
open RH_HilbertLimit.TwoRoutes

def nseNode (m : ℕ) : ℝ :=
  1 / (1 + (((m + 1 : ℕ) : ℝ) ^ 2))

def nseWeight (m : ℕ) : ℝ :=
  Real.exp (-(((m + 1 : ℕ) : ℝ)))

def nseAtom (m n : ℕ) : ℝ :=
  nseNode m ^ n

def nseReference (M n : ℕ) : ℝ :=
  ∑ m ∈ Finset.range M, nseWeight m * nseAtom m n

theorem nseNode_pos (m : ℕ) :
    0 < nseNode m := by
  unfold nseNode
  positivity

theorem nseNode_nonneg (m : ℕ) :
    0 ≤ nseNode m :=
  (nseNode_pos m).le

theorem nseNode_le_one (m : ℕ) :
    nseNode m ≤ 1 := by
  unfold nseNode
  have hden :
      0 < 1 + (((m + 1 : ℕ) : ℝ) ^ 2) := by
    positivity
  apply (div_le_iff₀ hden).2
  nlinarith [sq_nonneg (((m + 1 : ℕ) : ℝ))]

theorem nseWeight_pos (m : ℕ) :
    0 < nseWeight m := by
  unfold nseWeight
  exact Real.exp_pos _

theorem nseWeight_nonneg (m : ℕ) :
    0 ≤ nseWeight m :=
  (nseWeight_pos m).le

theorem momentFunctional_geometric
    (q : ℝ) (p : Polynomial ℝ) :
    momentFunctional (fun n : ℕ => q ^ n) p = p.eval q := by
  induction p using Polynomial.induction_on' with
  | add p s hp hs =>
      simp only [map_add, Polynomial.eval_add]
      rw [hp, hs]
  | monomial n c =>
      rw [momentFunctional_monomial]
      simp [Polynomial.eval_monomial]

theorem bernsteinWeight_geometric
    (q : ℝ) (N j : ℕ) :
    bernsteinWeight (fun n : ℕ => q ^ n) N j =
      (Nat.choose N j : ℝ) * q ^ j * (1 - q) ^ (N - j) := by
  rw [← momentFunctional_bernsteinPolynomial]
  rw [momentFunctional_geometric]
  simp [bernsteinPolynomial]

theorem geometric_bernsteinPositive
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    BernsteinPositive (fun n : ℕ => q ^ n) := by
  intro N j hj
  rw [bernsteinWeight_geometric]
  have h1q : 0 ≤ 1 - q := sub_nonneg.mpr hq1
  exact mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hq0 j))
    (pow_nonneg h1q (N - j))

theorem weighted_nseAtom_bernsteinPositive (m : ℕ) :
    BernsteinPositive (fun n => nseWeight m * nseAtom m n) := by
  unfold nseAtom
  exact bernsteinPositive_smul (nseWeight_nonneg m)
    (geometric_bernsteinPositive (nseNode_nonneg m) (nseNode_le_one m))

theorem nseReference_bernsteinPositive (M : ℕ) :
    BernsteinPositive (nseReference M) := by
  induction M with
  | zero =>
      have hzero :
          nseReference 0 = (fun _ : ℕ => (0 : ℝ)) := by
        funext n
        simp [nseReference]
      rw [hzero]
      exact bernsteinPositive_zero
  | succ M ih =>
      have hterm := weighted_nseAtom_bernsteinPositive M
      have hadd := bernsteinPositive_add ih hterm
      have href :
          nseReference (Nat.succ M) =
            (fun n =>
              nseReference M n + nseWeight M * nseAtom M n) := by
        funext n
        simp [nseReference, Finset.sum_range_succ, Nat.succ_eq_add_one]
      rw [href]
      exact hadd

end RHShiftedHausdorff.NSEJoint
