import CondEvolution
import CondConvolution
import CondRowSupport

namespace CondFeffA

open Fefferman Fefferman.ConcreteReal
open scoped BigOperators

noncomputable section

/-- Coefficient of amplitude degree k+2 produced by a fixed pair of lower
time rows in the nonlinear term. -/
def projectedCoefficient (n j k : ℕ) (x : RSpace) (i : Fin 3) : ℝ :=
  ∑ l ∈ Finset.range (k+1),
    projectedTransport (jetTable n j l) (jetTable n (n-j) (k-l)) x i

/-- Only the heat operator on the specific finite coefficient sums used by
the package is involved. The last summand has a zero input coefficient. -/
def HeatCoefficientExpansion (δ : ℝ) : Prop :=
  ∀ c ∈ Set.Ioo 0 δ, ∀ n x i,
    heatStep (evalField c n) x i =
      heatStep (jetTable n n 0) x i * c +
      ∑ k ∈ Finset.range (n+1), heatStep (jetTable n n (k+1)) x i * c^(k+2)

/-- Only the two prescribed lower-row operands of the projected transport
are involved. The RHS is the finite convolution of their coefficients. -/
def ProjectedCoefficientExpansion (δ : ℝ) : Prop :=
  ∀ c ∈ Set.Ioo 0 δ, ∀ n j, j ≤ n → ∀ x i,
    projectedTransport (evalField c j) (evalField c (n-j)) x i =
      ∑ k ∈ Finset.range (n+1), projectedCoefficient n j k x i * c^(k+2)

private theorem scalar_expansion (s : Finset ℕ) (a : ℝ) (h p b : ℕ → ℝ)
    (g : ℕ → ℕ → ℝ) :
    a + ∑ k ∈ s, (h k - ∑ j ∈ s, b j * g j k) * p k =
      (a + ∑ k ∈ s, h k * p k) - ∑ j ∈ s, b j * (∑ k ∈ s, g j k * p k) := by
  have hswitch : (∑ k ∈ s, (∑ j ∈ s, b j * g j k) * p k) =
      ∑ j ∈ s, b j * (∑ k ∈ s, g j k * p k) := by
    calc
      _ = ∑ k ∈ s, ∑ j ∈ s, b j * (g j k * p k) := by
        simp only [Finset.sum_mul, mul_assoc]
      _ = ∑ j ∈ s, ∑ k ∈ s, b j * (g j k * p k) := Finset.sum_comm
      _ = _ := by simp only [Finset.mul_sum]
  simp only [sub_mul, Finset.sum_sub_distrib, hswitch]
  ring

theorem finiteExpansionLaw_of_operator_expansions {δ : ℝ}
    (hheat : HeatCoefficientExpansion δ) (hproj : ProjectedCoefficientExpansion δ) :
    FiniteExpansionLaw δ := by
  intro c hc n
  funext x i
  have h0 : jetTable (n+1) (n+1) 0 x i = heatStep (jetTable n n 0) x i := by
    simp only [jetTable, if_pos rfl, Nat.zero_le, if_true, nextRow]
  have hk (k : ℕ) (hk : k ∈ Finset.range (n+1)) :
      jetTable (n+1) (n+1) (k+1) x i =
        heatStep (jetTable n n (k+1)) x i -
        ∑ j ∈ Finset.range (n+1), (n.choose j : ℝ) * projectedCoefficient n j k x i := by
    have hle : k+1 ≤ n+1 := Finset.mem_range.mp hk
    simp only [jetTable, if_pos rfl, if_pos hle, if_true, nextRow, projectedCoefficient]
  have hsum : (∑ j ∈ Finset.range (n+1), (n.choose j : ℝ) *
      projectedTransport (evalField c j) (evalField c (n-j)) x i) =
      ∑ j ∈ Finset.range (n+1), (n.choose j : ℝ) *
        (∑ k ∈ Finset.range (n+1), projectedCoefficient n j k x i * c^(k+2)) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [hproj c hc n j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)) x i]
  have hcoeff :
      (∑ k ∈ Finset.range (n+1), jetTable (n+1) (n+1) (k+1) x i * c^(k+2)) =
      ∑ k ∈ Finset.range (n+1), (heatStep (jetTable n n (k+1)) x i -
        ∑ j ∈ Finset.range (n+1), (n.choose j : ℝ) * projectedCoefficient n j k x i) * c^(k+2) := by
    apply Finset.sum_congr rfl
    intro k hkin
    rw [hk k hkin]
  change jetTable (n+1) (n+1) 0 x i * c + _ = heatStep (evalField c n) x i - _
  rw [h0, hcoeff, hheat c hc n x i, hsum]
  exact scalar_expansion (Finset.range (n+1)) _ _ _ _ _


private theorem sum_range_split {V : Type*} [AddCommMonoid V] (f : ℕ → V) (n : ℕ) :
    (∑ k ∈ Finset.range (n+1), f k) = f 0 + ∑ k ∈ Finset.range n, f (k+1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ f, ih, Finset.sum_range_succ (fun k => f (k+1))]
    simp [add_assoc]

/-- Either lower time row can be evaluated on a common finite set of
amplitude degrees; unused entries are provably zero. -/
theorem evalField_eq_row_sum (c : ℝ) {n j N : ℕ} (hj : j ≤ n) (hN : j ≤ N) :
    evalField c j = ∑ l ∈ Finset.range (N+1), c^(l+1) • jetTable n j l := by
  have base : evalField c j = ∑ l ∈ Finset.range (j+1), c^(l+1) • jetTable j j l := by
    rw [sum_range_split]
    funext x i
    simp [evalField, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm]
  rw [base, jetTable_row_stable hj]
  apply Finset.sum_subset
  · intro l hl
    exact Finset.mem_range.mpr (by have := Finset.mem_range.mp hl; omega)
  · intro l _ hl
    have hout : j < l := by
      by_contra! hle
      exact hl (Finset.mem_range.mpr (by omega))
    rw [jetTable_row_zero_of_lt (le_refl j) hout, smul_zero]

/-- Rowwise representatives agree with the physical heat operation only on
the selected expansion and its coefficient fields. The linear map may depend
on n, c, the spatial point and component. -/
def HeatRowLinearity (δ : ℝ) : Prop :=
  ∀ c ∈ Set.Ioo 0 δ, ∀ n x i, ∃ H : RInitial →ₗ[ℝ] ℝ,
    H (evalField c n) = heatStep (evalField c n) x i ∧
    ∀ l ≤ n+1, H (jetTable n n l) = heatStep (jetTable n n l) x i

/-- Rowwise representatives agree with the physical pressure-projected
transport on the sampled row pair and on the finitely many coefficient pairs. -/
def ProjectedRowBilinearity (δ : ℝ) : Prop :=
  ∀ c ∈ Set.Ioo 0 δ, ∀ n j, j ≤ n → ∀ x i,
    ∃ B : RInitial →ₗ[ℝ] RInitial →ₗ[ℝ] ℝ,
      B (evalField c j) (evalField c (n-j)) =
        projectedTransport (evalField c j) (evalField c (n-j)) x i ∧
      ∀ l ≤ n, ∀ r ≤ n, B (jetTable n j l) (jetTable n (n-j) r) =
        projectedTransport (jetTable n j l) (jetTable n (n-j) r) x i

theorem heatExpansion_of_rowLinearity {δ : ℝ} (h : HeatRowLinearity δ) :
    HeatCoefficientExpansion δ := by
  intro c hc n x i
  obtain ⟨H, hmain, hrow⟩ := h c hc n x i
  rw [← hmain, evalField_eq_row_sum c (le_refl n) (Nat.le_succ n), map_sum]
  simp only [map_smul, smul_eq_mul]
  rw [sum_range_split]
  simp only [Nat.zero_add, pow_one, hrow 0 (Nat.zero_le _)]
  rw [mul_comm c]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k+1 ≤ n+1 := Finset.mem_range.mp hk
  rw [hrow (k+1) hk', mul_comm]

theorem projectedExpansion_of_rowBilinearity {δ : ℝ} (h : ProjectedRowBilinearity δ) :
    ProjectedCoefficientExpansion δ := by
  intro c hc n j hj x i
  obtain ⟨B, hmain, hrow⟩ := h c hc n j hj x i
  let S := Finset.range (n+1)
  let F := fun l r : ℕ =>
    projectedTransport (jetTable n j l) (jetTable n (n-j) r) x i *
      (c^(l+1) * c^(r+1))
  have hb (l : ℕ) (hl : l ∈ S) :
      B (jetTable n j l) (evalField c (n-j)) =
        ∑ r ∈ S, (c^(r+1) *
          projectedTransport (jetTable n j l) (jetTable n (n-j) r) x i) := by
    rw [evalField_eq_row_sum c (Nat.sub_le n j) (Nat.sub_le n j), map_sum]
    apply Finset.sum_congr rfl
    intro r hr
    have hl' : l ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hl)
    have hr' : r ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hr)
    rw [map_smul, smul_eq_mul, hrow l hl' r hr']
  have hrect : projectedTransport (evalField c j) (evalField c (n-j)) x i =
      ∑ l ∈ S, ∑ r ∈ S, F l r := by
    rw [← hmain]
    change B.flip (evalField c (n-j)) (evalField c j) = _
    rw [evalField_eq_row_sum c hj hj, map_sum]
    apply Finset.sum_congr rfl
    intro l hl
    rw [map_smul, smul_eq_mul]
    change c^(l+1) * B (jetTable n j l) (evalField c (n-j)) = _
    rw [hb l hl, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    dsimp [F]
    ring
  have hdiag : (∑ k ∈ S, projectedCoefficient n j k x i * c^(k+2)) =
      ∑ k ∈ S, ∑ l ∈ Finset.range (k+1), F l (k-l) := by
    apply Finset.sum_congr rfl
    intro k _
    rw [projectedCoefficient, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro l hl
    have hl' := Finset.mem_range.mp hl
    dsimp [F]
    rw [← pow_add, show (l+1)+(k-l+1) = k+2 by omega]
  rw [hrect, hdiag, triangular_convolution]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro r _
  by_cases hk : l+r ≤ n
  · simp only [hk, if_true]
  · have hz := projected_cross_zero (l := l) (r := r) hj (by omega)
    simp [F, hk, hz]

/-- The complete combinatorial expansion follows from finite linearity and
finite bilinearity on the physical coefficient fields. -/
theorem finiteExpansionLaw_of_row_operators {δ : ℝ}
    (hheat : HeatRowLinearity δ) (hproj : ProjectedRowBilinearity δ) :
    FiniteExpansionLaw δ :=
  finiteExpansionLaw_of_operator_expansions
    (heatExpansion_of_rowLinearity hheat) (projectedExpansion_of_rowBilinearity hproj)

end
end CondFeffA

#print axioms CondFeffA.finiteExpansionLaw_of_operator_expansions

#print axioms CondFeffA.finiteExpansionLaw_of_row_operators
