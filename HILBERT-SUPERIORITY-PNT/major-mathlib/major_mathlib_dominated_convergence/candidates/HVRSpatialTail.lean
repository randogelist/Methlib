import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

/-!
An integrable kernel has vanishing one-sided tails. This is a preparatory
piece for the spatial Abel damping argument, not the damping theorem itself.
The proof uses continuity of set integrals from above for nested sets. The
selected dominated-convergence declarations are not called in this source;
recursive dependency coverage is not yet established. No Lean build or audit
has been performed for this source.
-/
noncomputable section
open Filter MeasureTheory
open scoped Topology

namespace HVRSpatialTail

def positiveTail (n : ℕ) : Set ℝ := Set.Ioi (n : ℝ)

theorem positiveTail_antitone : Antitone positiveTail := by
  intro m n hmn x hx
  change (m : ℝ) < x
  change (n : ℝ) < x at hx
  have hmn' : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
  exact lt_of_le_of_lt hmn' hx

theorem positiveTail_iInter : (⋂ n : ℕ, positiveTail n) = ∅ := by
  apply Set.Subset.antisymm ?_ (Set.empty_subset _)
  intro x hx
  change False
  have hall : ∀ n : ℕ, x ∈ positiveTail n := Set.mem_iInter.mp hx
  obtain ⟨n, hn⟩ := exists_nat_gt x
  have hx' : (n : ℝ) < x := hall n
  linarith

/-- Tail integral of any integrable real function tends to zero. -/
theorem tail_integral_tendsto_zero (w : ℝ → ℝ) (hw : Integrable w volume) :
    Tendsto (fun n : ℕ => ∫ u : ℝ in positiveTail n, w u) atTop (𝓝 0) := by
  have hmeas : ∀ n : ℕ, MeasurableSet (positiveTail n) := by
    intro n
    exact measurableSet_Ioi
  have hi : ∃ n : ℕ, IntegrableOn w (positiveTail n) volume := by
    refine ⟨0, ?_⟩
    exact hw.mono_measure Measure.restrict_le_self
  have ht := tendsto_setIntegral_of_antitone hmeas positiveTail_antitone hi
  simpa only [positiveTail_iInter, setIntegral_empty] using ht

/-- Given a fixed shift, the positive tail of an L1 kernel can be made small. -/
theorem shifted_kernel_tail_small (K : ℝ → ℂ) (hK : Integrable K volume)
    (x ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, (∫ u : ℝ in positiveTail N, ‖K (x - u)‖) < ε := by
  have hw : Integrable (fun u : ℝ => ‖K (x - u)‖) volume := (hK.comp_sub_left x).norm
  have h := (tail_integral_tendsto_zero _ hw).eventually (eventually_lt_nhds hε)
  exact h.exists

/-- Cumulative integrals of an L1 function exhaust its integral using
    monotone set-integral convergence. -/
theorem cumulative_integral_tendsto_total (k : ℝ → ℝ) (hk : Integrable k volume) :
    Tendsto (fun x : ℝ => ∫ t : ℝ in Set.Iic x, k t) atTop (𝓝 (∫ t : ℝ, k t)) := by
  have hmeas : ∀ x : ℝ, MeasurableSet (Set.Iic x) := fun _ => measurableSet_Iic
  have hmono : Monotone (fun x : ℝ => Set.Iic x) := by
    intro a b hab t ht
    exact le_trans ht hab
  have hunion : (⋃ x : ℝ, Set.Iic x) = Set.univ := by
    ext t
    simp only [Set.mem_iUnion, Set.mem_Iic, Set.mem_univ, iff_true]
    exact ⟨t, le_rfl⟩
  have hi : IntegrableOn k (⋃ x : ℝ, Set.Iic x) volume := by
    rw [hunion]
    exact hk.integrableOn
  have ht := tendsto_setIntegral_of_monotone hmeas hmono hi
  simpa only [hunion, setIntegral_univ] using ht

end HVRSpatialTail
