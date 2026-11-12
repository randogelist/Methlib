import QuasiFeffermanB.ThetaGaussian
import SingularClosure.LerayPressure

/-! Finite actual three-dimensional Galerkin lattice Gaussian envelope. -/

set_option autoImplicit false
set_option Elab.async true

open scoped BigOperators

namespace QuasiFeffermanB
open SingularClosure
noncomputable section

private def latticeBox (N : ℕ) : Finset Frequency :=
  let s : Finset ℤ := Finset.Icc (-(N : ℤ)) (N : ℤ)
  ((s.product s).product s).image
    (fun q : (ℤ × ℤ) × ℤ => ![q.1.1, q.1.2, q.2])

private theorem tuple_frequency_injective :
    Function.Injective (fun q : (ℤ × ℤ) × ℤ => (![q.1.1, q.1.2, q.2] : Frequency)) := by
  intro p q h
  have h0 := congrFun h (0 : Fin 3)
  have h1 := congrFun h (1 : Fin 3)
  have h2 := congrFun h (2 : Fin 3)
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] at h0 h1 h2
  exact Prod.ext (Prod.ext h0 h1) h2

private theorem zero_mem_latticeBox (N : ℕ) : (0 : Frequency) ∈ latticeBox N := by
  unfold latticeBox
  apply Finset.mem_image.mpr
  refine ⟨((0, 0), 0), ?_, ?_⟩
  · simp
  · ext i
    fin_cases i <;> rfl

private theorem cutoffModes_subset_latticeBox (N : ℕ) : cutoffModes N ⊆ latticeBox N := by
  exact Finset.filter_subset _ _

private theorem latticeBox_gaussian_sum (N : ℕ) (t : ℝ) :
    (∑ k ∈ latticeBox N,
      Real.exp (-Real.pi * t * (galerkinFreqSq k : ℝ))) =
    (∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), Real.exp (-Real.pi * t * (n : ℝ) ^ 2)) ^ 3 := by
  have hfactor (a b c : ℤ) :
      Real.exp (-Real.pi * t * (galerkinFreqSq ![a, b, c] : ℝ)) =
      Real.exp (-Real.pi * t * (a : ℝ) ^ 2) *
        Real.exp (-Real.pi * t * (b : ℝ) ^ 2) *
          Real.exp (-Real.pi * t * (c : ℝ) ^ 2) := by
    simp only [galerkinFreqSq, Fin.sum_univ_succ]
    push_cast
    simp only [mul_add, Real.exp_add, add_zero]
    ring
  unfold latticeBox
  rw [Finset.sum_image (fun _ _ _ _ h => tuple_frequency_injective h)]
  simp only [Finset.sum_product, hfactor]
  simp only [← Finset.mul_sum, ← Finset.sum_mul]
  ring

/-- Finite nonzero Galerkin Gaussian sums satisfy the exact normalized
three-dimensional theta envelope. -/
theorem FINITE_LATTICE_GAUSSIAN_ENVELOPE
    (N : ℕ) (t : ℝ) (ht : 0 < t) :
    (∑ k ∈ cutoffModes N,
      Real.exp (-Real.pi * t * (galerkinFreqSq k : ℝ))) ≤ t ^ (-3 / 2 : ℝ) := by
  have hsub : insert (0 : Frequency) (cutoffModes N) ⊆ latticeBox N := by
    intro k hk
    rcases Finset.mem_insert.mp hk with rfl | hk
    · exact zero_mem_latticeBox N
    · exact cutoffModes_subset_latticeBox N hk
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun k _ _ => (Real.exp_pos (-Real.pi * t * (galerkinFreqSq k : ℝ))).le)
  rw [Finset.sum_insert (cutoffModes_zero_not_mem N)] at hsum
  have hzero : Real.exp (-Real.pi * t * (galerkinFreqSq (0 : Frequency) : ℝ)) = 1 := by
    simp [galerkinFreqSq]
  rw [hzero, latticeBox_gaussian_sum N t] at hsum
  have hone :
      (∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), Real.exp (-Real.pi * t * (n : ℝ) ^ 2)) ≤
      gaussianThetaOne t :=
    (gaussianThetaOne_summable t ht).sum_le_tsum _
      (fun n _ => (Real.exp_pos _).le)
  have hnonneg : 0 ≤
      ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), Real.exp (-Real.pi * t * (n : ℝ) ^ 2) :=
    Finset.sum_nonneg (fun n _ => (Real.exp_pos _).le)
  have hcube := pow_le_pow_left₀ hnonneg hone 3
  have henv := GAUSSIAN_THETA_CUBE_ENVELOPE t ht
  linarith

end
end QuasiFeffermanB
