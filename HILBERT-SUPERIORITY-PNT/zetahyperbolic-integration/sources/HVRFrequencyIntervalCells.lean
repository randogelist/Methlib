import HVRFrequencyCellBudget
import Mathlib.Order.Interval.Set.Union

/-!
Finite interval geometry for HVR frequency quadrature.

For each real R ≥ 0 and positive N, the N half-open intervals between the
regular grid points -R + i(2R/N) are measurable and pairwise disjoint, cover
(-R,R], and have distance at most 2R/N from the left-endpoint sample. These
are the geometric inputs needed by the existing finite-cell error estimate.
No claim is made here about integrability of the oscillatory modes, the
mesh-to-zero limit, the swap of two integrals, or PNT. No Lean was run locally.
-/

noncomputable section
open Filter MeasureTheory
open scoped BigOperators

namespace HVRFrequencyIntervalCells

def gridPoint (R : ℝ) (N i : ℕ) : ℝ :=
  -R + (i : ℝ) * (2 * R / (N : ℝ))

def gridCell (R : ℝ) (N i : ℕ) : Set ℝ :=
  Set.Ioc (gridPoint R N i) (gridPoint R N (i + 1))

theorem gridPoint_zero (R : ℝ) (N : ℕ) : gridPoint R N 0 = -R := by
  simp [gridPoint]

theorem gridPoint_end (R : ℝ) (N : ℕ) (hN : 0 < N) :
    gridPoint R N N = R := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  unfold gridPoint
  field_simp
  <;> ring

theorem gridPoint_step (R : ℝ) (N i : ℕ) :
    gridPoint R N (i + 1) - gridPoint R N i = 2 * R / (N : ℝ) := by
  simp only [gridPoint, Nat.cast_add, Nat.cast_one]
  ring

theorem gridPoint_monotone (R : ℝ) (N : ℕ) (hR : 0 ≤ R) :
    Monotone (gridPoint R N) := by
  intro i j hij
  have hreal : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
  have hstep : 0 ≤ 2 * R / (N : ℝ) := by positivity
  exact add_le_add_left (mul_le_mul_of_nonneg_right hreal hstep) (-R)

/-- The grid intervals are pairwise disjoint even though their endpoints
touch. -/
theorem gridCells_pairwise_disjoint (R : ℝ) (N : ℕ) (hR : 0 ≤ R) :
    Set.Pairwise (↑(Finset.range N) : Set ℕ) (fun i j => Disjoint (gridCell R N i) (gridCell R N j)) := by
  intro i hi j hj hij
  change Disjoint (Set.Ioc (gridPoint R N i) (gridPoint R N (i + 1)))
    (Set.Ioc (gridPoint R N j) (gridPoint R N (j + 1)))
  apply Set.disjoint_left.2
  intro t hti htj
  rcases lt_or_gt_of_ne hij with hij | hji
  · have hij' : i + 1 ≤ j := by omega
    have hsep := gridPoint_monotone R N hR hij'
    exact not_lt_of_ge (le_trans hti.2 hsep) htj.1
  · have hji' : j + 1 ≤ i := by omega
    have hsep := gridPoint_monotone R N hR hji'
    exact not_lt_of_ge (le_trans htj.2 hsep) hti.1

theorem gridCells_measurable (R : ℝ) (N i : ℕ) :
    MeasurableSet (gridCell R N i) := measurableSet_Ioc

/-- Every point in (-R,R] lies in one of the N grid cells. -/
theorem gridCells_cover (R : ℝ) (N : ℕ) (hN : 0 < N) :
    Set.Ioc (-R) R ⊆ ⋃ i ∈ Finset.range N, gridCell R N i := by
  have h := Ioc_subset_biUnion_Ioc N (gridPoint R N)
  rw [gridPoint_zero, gridPoint_end R N hN] at h
  simpa only [gridCell] using h

/-- Every point in an occupied cell is within one mesh of its sample. -/
theorem gridCell_close (R : ℝ) (N i : ℕ) (t : ℝ)
    (ht : t ∈ gridCell R N i) :
    |t - gridPoint R N i| ≤ 2 * R / (N : ℝ) := by
  change gridPoint R N i < t ∧ t ≤ gridPoint R N (i + 1) at ht
  rw [abs_of_nonneg (sub_nonneg.mpr (le_of_lt ht.1))]
  have hstep := gridPoint_step R N i
  linarith

theorem gridCells_close_ae {μ : Measure ℝ} (R : ℝ) (N : ℕ) :
    ∀ i ∈ Finset.range N, ∀ᵐ t : ℝ ∂μ.restrict (gridCell R N i),
      |t - gridPoint R N i| ≤ 2 * R / (N : ℝ) := by
  intro i hi
  filter_upwards [ae_restrict_mem (gridCells_measurable R N i)] with t ht
  exact gridCell_close R N i t ht

end HVRFrequencyIntervalCells
