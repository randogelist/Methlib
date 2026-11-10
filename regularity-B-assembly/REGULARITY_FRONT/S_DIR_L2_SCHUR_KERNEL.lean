import S_DIR_L2_SCHUR_FRONTIER

set_option autoImplicit false
set_option maxHeartbeats 0

open scoped BigOperators

noncomputable section

namespace SDirL2

/-!
# Finite concrete heat-kernel Schur bridge for S_DIR_L2

The radial parameter `r i` is positive on every included index. The
kernel `1/(r_i²+r_j²)` is the time-integrated pair of heat modes after
factoring out `4π²ν`. Its nonnegative and symmetric algebra is proved
below, as is the exact finite quadratic estimate.

IMPORTANT: The uniform annular lattice count and the resulting Schur
row estimate are NOT asserted by this module. The row estimate stays a
named premise, to be discharged by the future geometric lattice proof.
-/

/-- Symmetric nonnegative heat correlation kernel on positive radii. -/
def abstractHeatKernel {ι : Type*} (r : ι → ℝ) (i j : ι) : ℝ :=
  1 / (r i ^ 2 + r j ^ 2)

theorem S_DIR_L2_ABSTRACT_KERNEL_NONNEG
    {ι : Type*} (r : ι → ℝ) (i j : ι)
    (hi : 0 < r i) (hj : 0 < r j) :
    0 ≤ abstractHeatKernel r i j := by
  unfold abstractHeatKernel
  positivity

theorem S_DIR_L2_ABSTRACT_KERNEL_SYMMETRIC
    {ι : Type*} (r : ι → ℝ) (i j : ι) :
    abstractHeatKernel r i j = abstractHeatKernel r j i := by
  simp only [abstractHeatKernel, add_comm]

/--
Exact finite Schur bound for the heat correlation kernel.

`hRow` is an explicit analytic/geometric premise:
   sum_j K(i,j)/r_j <= C/r_i.
The proof never assumes that this premise has been established for all
rank-two directional lattice planes. That remains the infinite-row edge.
-/
theorem S_DIR_L2_FINITE_HEAT_KERNEL_SCHUR
    {ι : Type*} [DecidableEq ι]
    (F : Finset ι) (r b : ι → ℝ) (C : ℝ)
    (hr : ∀ i ∈ F, 0 < r i)
    (hRow : ∀ i ∈ F,
      (∑ j ∈ F, abstractHeatKernel r i j * (r j)⁻¹)
        ≤ C * (r i)⁻¹) :
    (∑ i ∈ F, ∑ j ∈ F, abstractHeatKernel r i j * b i * b j)
      ≤ C * ∑ i ∈ F, (b i) ^ 2 := by
  have hinv (i : ι) (hi : i ∈ F) : (r i)⁻¹ * r i = 1 := by
    field_simp [ne_of_gt (hr i hi)]
  have hSchur :
      (∑ i ∈ F, ∑ j ∈ F,
        (abstractHeatKernel r i j * (r i)⁻¹ * (r j)⁻¹) *
          ((r i * b i) * (r j * b j)))
        ≤ C * ∑ i ∈ F, ((r i)⁻¹ * (r i * b i)) ^ 2 := by
    apply S_DIR_L2_WEIGHTED_FINITE_SCHUR F
      (abstractHeatKernel r)
      (fun i => (r i)⁻¹)
      (fun i => r i * b i) C
    · intro i hi j hj
      exact S_DIR_L2_ABSTRACT_KERNEL_NONNEG r i j (hr i hi) (hr j hj)
    · intro i hi j hj
      exact S_DIR_L2_ABSTRACT_KERNEL_SYMMETRIC r i j
    · intro i hi
      exact inv_pos.mpr (hr i hi)
    · exact hRow
  have hSumEq :
      (∑ i ∈ F, ∑ j ∈ F,
        (abstractHeatKernel r i j * (r i)⁻¹ * (r j)⁻¹) *
          ((r i * b i) * (r j * b j)))
        = (∑ i ∈ F, ∑ j ∈ F,
            abstractHeatKernel r i j * b i * b j) := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    calc
      (abstractHeatKernel r i j * (r i)⁻¹ * (r j)⁻¹) *
          ((r i * b i) * (r j * b j))
          = abstractHeatKernel r i j * ((r i)⁻¹ * r i) *
              ((r j)⁻¹ * r j) * b i * b j := by ring
      _ = abstractHeatKernel r i j * b i * b j := by
        rw [hinv i hi, hinv j hj]
        ring
  have hRhs :
      C * (∑ i ∈ F, ((r i)⁻¹ * (r i * b i)) ^ 2)
        = C * (∑ i ∈ F, (b i) ^ 2) := by
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [← mul_assoc, hinv i hi, one_mul]
  calc
    (∑ i ∈ F, ∑ j ∈ F, abstractHeatKernel r i j * b i * b j)
        = (∑ i ∈ F, ∑ j ∈ F,
            (abstractHeatKernel r i j * (r i)⁻¹ * (r j)⁻¹) *
              ((r i * b i) * (r j * b j))) := hSumEq.symm
    _ ≤ C * ∑ i ∈ F, ((r i)⁻¹ * (r i * b i)) ^ 2 := hSchur
    _ = C * ∑ i ∈ F, (b i) ^ 2 := hRhs

/-- The arithmetic normalization of the B-tier global Serrin constant. -/
theorem S_DIR_L2_SERRIN_CONSTANT_NORMALIZATION
    (ν : ℝ) (hν : 0 < ν) :
    (1 / (4 * Real.pi ^ 2 * ν)) * (45 * Real.pi / 2)
      = 45 / (8 * Real.pi * ν) := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hv : ν ≠ 0 := ne_of_gt hν
  field_simp [hpi, hv]
  ring

end SDirL2
