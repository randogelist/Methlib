import HVR_PhysicalKernel_WindowAlgebra
import Mathlib.MeasureTheory.Integral.Bochner.Set

noncomputable section
open Filter MeasureTheory HVRPhysicalKernelCandidate HVRPhysicalKernelWindowAlgebra
open scoped Topology

/-! Candidate integrable-tail estimate for the actual normalized physical
kernel. It proves tails outside expanding symmetric intervals tend to zero.
The affine change of variables relating this tail to a concentrated scaled
kernel remains to be proved. No local Lean execution. -/
namespace HVRPhysicalKernelTail

def symmetricTail (n : ℕ) : Set ℝ := (Set.Icc (-(n : ℝ)) (n : ℝ))ᶜ

theorem symmetricTail_antitone : Antitone symmetricTail := by
  intro m n hmn x hx
  change x ∉ Set.Icc (-(m : ℝ)) (m : ℝ)
  change x ∉ Set.Icc (-(n : ℝ)) (n : ℝ) at hx
  intro hm
  apply hx
  have hmn' : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
  exact ⟨by linarith [hm.1], by linarith [hm.2]⟩

theorem symmetricTail_iInter : (⋂ n : ℕ, symmetricTail n) = ∅ := by
  apply Set.Subset.antisymm ?_ (Set.empty_subset _)
  intro x hx
  change False
  have hall : ∀ n : ℕ, x ∈ symmetricTail n := Set.mem_iInter.mp hx
  obtain ⟨n, hn⟩ := exists_nat_gt |x|
  have hx' := hall n
  change x ∉ Set.Icc (-(n : ℝ)) (n : ℝ) at hx'
  apply hx'
  have hb := abs_lt.mp hn
  exact ⟨le_of_lt hb.1, le_of_lt hb.2⟩

/-- Integrability implies the actual kernel mass in symmetric tails vanishes. -/
theorem normalizedKernel_symmetricTail_tendsto (w : ℝ) (hw : 0 < w) :
    Tendsto (fun n : ℕ => ∫ x : ℝ in symmetricTail n, normalizedKernel w hw x)
      atTop (𝓝 0) := by
  have hmeas : ∀ n : ℕ, MeasurableSet (symmetricTail n) := by
    intro n
    exact measurableSet_Icc.compl
  have hi : ∃ n : ℕ, IntegrableOn (normalizedKernel w hw) (symmetricTail n) volume := by
    refine ⟨0, ?_⟩
    exact (normalizedKernel_integrable w hw).mono_measure Measure.restrict_le_self
  have ht := tendsto_setIntegral_of_antitone hmeas symmetricTail_antitone hi
  simpa only [symmetricTail_iInter, setIntegral_empty] using ht

/-- Consequently every positive tolerance has a finite symmetric cutoff. -/
theorem normalizedKernel_exists_small_tail (w : ℝ) (hw : 0 < w)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, (∫ x : ℝ in symmetricTail n, normalizedKernel w hw x) < ε := by
  have h := (normalizedKernel_symmetricTail_tendsto w hw).eventually (eventually_lt_nhds hε)
  exact h.exists

/-- A point outside the window maps outside the chosen symmetric cutoff
under a sufficiently large positive dilation about the window midpoint. -/
theorem outside_window_scaled (h N R x : ℝ) (hh : 0 < h) (hN : 0 < N)
    (hR : 0 ≤ R) (hscale : 2 * R ≤ N * h)
    (hx : x ∉ Set.Icc 0 h) : R < |N * (x - h / 2)| := by
  by_cases hx0 : x < 0
  · have hneg : N * x < 0 := mul_neg_of_pos_of_neg hN hx0
    have hy : N * (x - h / 2) < 0 := by nlinarith
    rw [abs_of_neg hy]
    nlinarith
  · have hxlo : 0 ≤ x := le_of_not_gt hx0
    have hxhi : h < x := by
      by_contra hn
      exact hx ⟨hxlo, le_of_not_gt hn⟩
    have hpos : 0 < N * (x - h) := mul_pos hN (sub_pos.mpr hxhi)
    have hy : 0 ≤ N * (x - h / 2) := by nlinarith
    rw [abs_of_nonneg hy]
    nlinarith

end HVRPhysicalKernelTail
