import CondRecurrence

namespace CondFeffA

open Fefferman Fefferman.ConcreteReal
open scoped BigOperators

private theorem row_partial_zero (i : Fin 3) :
    spatialDerivative i (fun _ : RSpace => (0 : ℝ)) = (fun _ : RSpace => (0 : ℝ)) := by
  funext x
  change (fderiv ℝ (fun _ : RSpace => (0 : ℝ)) x) (basisDirection i) = 0
  rw [fderiv_const_apply] <;> rfl

private theorem heatStep_zero_row : heatStep 0 = 0 := by
  funext x i
  let z := fun _ : RSpace => (0 : ℝ)
  change spatialDerivative 0 (spatialDerivative 0 z) x +
    spatialDerivative 1 (spatialDerivative 1 z) x +
    spatialDerivative 2 (spatialDerivative 2 z) x = 0
  simp only [z, row_partial_zero, add_zero]

private theorem zero_projected_of_transport {v w : RInitial} (h : transport v w = 0) :
    projectedTransport v w = 0 := by
  let z := fun _ : RSpace => (0 : ℝ)
  have hdiv : fieldDiv 0 = z := by
    funext x
    change spatialDerivative 0 z x + spatialDerivative 1 z x + spatialDerivative 2 z x = 0
    simp only [z, row_partial_zero, add_zero]
  have hpot : newtonPotential z = z := by
    funext x
    simp [newtonPotential, z]
  funext x i
  change transport v w x i + spatialDerivative i (newtonPotential (fieldDiv (transport v w))) x = 0
  rw [h, hdiv, hpot]
  simp [z, row_partial_zero]

theorem projectedTransport_zero_left (w : RInitial) : projectedTransport 0 w = 0 := by
  apply zero_projected_of_transport
  funext x i
  simp [transport, sum3]

theorem projectedTransport_zero_right (v : RInitial) : projectedTransport v 0 = 0 := by
  apply zero_projected_of_transport
  funext x i
  simp [transport, sum3, spatialDerivative]

/-- Later stages retain every row already constructed. -/
theorem jetTable_row_stable {n j : ℕ} (hj : j ≤ n) :
    jetTable n j = jetTable j j := by
  induction n generalizing j with
  | zero =>
    have h : j = 0 := by omega
    subst j
    rfl
  | succ n ih =>
    by_cases h : j = n+1
    · subst j
      rfl
    · simpa only [jetTable, if_neg h] using ih (j := j) (by omega)

private theorem nextRow_zero_of_bound (n k : ℕ) (T : JetTable)
    (hb : ∀ j : ℕ, j ≤ n → ∀ r : ℕ, j < r → T j r = 0) (hk : n < k) :
    nextRow n T (k+1) = 0 := by
  funext x i
  have inner (j : ℕ) (hj : j ∈ Finset.range (n+1)) :
      (∑ l ∈ Finset.range (k+1), projectedTransport (T j l) (T (n-j) (k-l)) x i) = 0 := by
    apply Finset.sum_eq_zero
    intro l hl
    have hjn := Finset.mem_range.mp hj
    have hlk := Finset.mem_range.mp hl
    by_cases hjl : j < l
    · simp [hb j (by omega) l hjl, projectedTransport_zero_left]
    · have hr : n-j < k-l := by omega
      simp [hb (n-j) (by omega) (k-l) hr, projectedTransport_zero_right]
  have outer :
      (∑ j ∈ Finset.range (n+1), (n.choose j : ℝ) *
        ∑ l ∈ Finset.range (k+1), projectedTransport (T j l) (T (n-j) (k-l)) x i) = 0 := by
    exact Finset.sum_eq_zero (fun j hj => by rw [inner j hj, mul_zero])
  simp only [nextRow, hb n le_rfl (k+1) (by omega), heatStep_zero_row, outer,
    Pi.zero_apply, sub_zero]

/-- A row of time order j has amplitude degree at most j+1; column k encodes degree k+1. -/
theorem jetTable_row_zero_of_lt {n j k : ℕ} (hj : j ≤ n) (hk : j < k) :
    jetTable n j k = 0 := by
  induction n generalizing j k with
  | zero =>
    have hj0 : j = 0 := by omega
    subst j
    have hk0 : k ≠ 0 := by omega
    simp [jetTable, hk0]
  | succ n ih =>
    by_cases h : j = n+1
    · subst j
      have hout : ¬ k ≤ n+1 := by omega
      simp [jetTable, hout]
    · simpa only [jetTable, if_neg h] using ih (j := j) (k := k) (by omega) hk

theorem projected_cross_zero {n j l r : ℕ} (hj : j ≤ n) (hs : n < l+r) :
    projectedTransport (jetTable n j l) (jetTable n (n-j) r) = 0 := by
  by_cases hl : j < l
  · rw [jetTable_row_zero_of_lt hj hl, projectedTransport_zero_left]
  · have hr : n-j < r := by omega
    rw [jetTable_row_zero_of_lt (n := n) (j := n-j) (by omega) hr,
      projectedTransport_zero_right]

end CondFeffA

#print axioms CondFeffA.projectedTransport_zero_left
#print axioms CondFeffA.projectedTransport_zero_right
#print axioms CondFeffA.jetTable_row_stable
#print axioms CondFeffA.jetTable_row_zero_of_lt
#print axioms CondFeffA.projected_cross_zero
