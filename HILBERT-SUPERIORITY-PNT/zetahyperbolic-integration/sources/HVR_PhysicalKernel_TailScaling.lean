import HVR_PhysicalKernel_Tail
import HVR_PhysicalKernel_ScaledTranslate
import HVR_PhysicalKernel_CanonicalWindow
import Mathlib.MeasureTheory.Integral.Bochner.Set

noncomputable section
open Filter MeasureTheory HVRPhysicalKernelCandidate HVRPhysicalKernelWindowAlgebra
open HVRPhysicalKernelTail HVRPhysicalKernelScaledTranslate HVRPhysicalKernelCanonicalWindow
open scoped Topology

/-! Candidate affine-tail bound and concentrated actual normalized kernels.
The proof uses an indicator majorant and a whole-line change of variables.
The smoothing limits and Fourier representation remain unproved.
No Lean was run locally; the pinned cache must externally validate this file. -/
namespace HVRPhysicalKernelTailScaling

/-- The affine window tail is bounded by an unscaled symmetric tail. -/
theorem scaled_window_tail_le (w : ℝ) (hw : 0 < w)
    (h N : ℝ) (hh : 0 < h) (hN : 0 < N) (n : ℕ)
    (hscale : 2 * (n : ℝ) ≤ N * h) :
    (∫ x : ℝ in (Set.Icc 0 h)ᶜ, scaledTranslate w hw N (h / 2) x) ≤
      ∫ x : ℝ in symmetricTail n, normalizedKernel w hw x := by
  let F : ℝ → ℝ := (symmetricTail n).indicator (normalizedKernel w hw)
  have hmeas : MeasurableSet (symmetricTail n) := measurableSet_Icc.compl
  have hF : Integrable F volume := (normalizedKernel_integrable w hw).indicator hmeas
  have hshift : Integrable (fun x : ℝ => N * F (N * (x - h / 2))) volume := by
    have hs := (hF.comp_mul_left' (ne_of_gt hN)).comp_sub_right (h / 2)
    exact hs.const_mul N
  have hFnonneg : ∀ x : ℝ, 0 ≤ F x := by
    intro x
    by_cases hx : x ∈ symmetricTail n
    · simp only [F, Set.indicator_of_mem hx]
      exact normalizedKernel_nonneg_unconditional w hw x
    · simp [F, Set.indicator_of_notMem hx]
  have hshift_nonneg : ∀ x : ℝ, 0 ≤ N * F (N * (x - h / 2)) := by
    intro x
    exact mul_nonneg (le_of_lt hN) (hFnonneg _)
  have htotal : (∫ x : ℝ, N * F (N * (x - h / 2))) =
      ∫ x : ℝ in symmetricTail n, normalizedKernel w hw x := by
    rw [integral_const_mul]
    rw [integral_sub_right_eq_self (fun x : ℝ => F (N * x)) (h / 2)]
    rw [Measure.integral_comp_mul_left]
    simp only [abs_of_pos (inv_pos.mpr hN), smul_eq_mul]
    rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hN), one_mul]
    exact integral_indicator hmeas
  calc
    (∫ x : ℝ in (Set.Icc 0 h)ᶜ, scaledTranslate w hw N (h / 2) x) ≤
        ∫ x : ℝ in (Set.Icc 0 h)ᶜ, N * F (N * (x - h / 2)) := by
      apply setIntegral_mono_on
        ((scaledTranslate_integrable w hw N (h / 2) hN).mono_measure Measure.restrict_le_self)
        (hshift.mono_measure Measure.restrict_le_self) measurableSet_Icc.compl
      intro x hx
      have houtside : (n : ℝ) < |N * (x - h / 2)| :=
        outside_window_scaled h N n x hh hN (by exact_mod_cast (Nat.zero_le n)) hscale hx
      have hmem : N * (x - h / 2) ∈ symmetricTail n := by
        change N * (x - h / 2) ∉ Set.Icc (-(n : ℝ)) (n : ℝ)
        intro hi
        have habs : |N * (x - h / 2)| ≤ (n : ℝ) := abs_le.mpr ⟨hi.1, hi.2⟩
        linarith
      simp only [scaledTranslate, F, Set.indicator_of_mem hmem, le_refl]
    _ ≤ ∫ x : ℝ, N * F (N * (x - h / 2)) :=
      setIntegral_le_integral hshift (Filter.Eventually.of_forall hshift_nonneg)
    _ = _ := htotal

/-- Every positive window and tail tolerance admit a concrete affine rescale
of the actual physical kernel with that small window complement mass. -/
theorem exists_scaled_window_small_tail (w : ℝ) (hw : 0 < w)
    (h ε : ℝ) (hh : 0 < h) (hε : 0 < ε) :
    ∃ N : ℝ, 0 < N ∧
      (∫ x : ℝ in (Set.Icc 0 h)ᶜ, scaledTranslate w hw N (h / 2) x) < ε := by
  obtain ⟨n, hn⟩ := normalizedKernel_exists_small_tail w hw ε hε
  let N : ℝ := 2 * (n : ℝ) / h + 1
  have hn0 : (0 : ℝ) ≤ n := by exact_mod_cast (Nat.zero_le n)
  have hN : 0 < N := by dsimp [N]; positivity
  have hscale : 2 * (n : ℝ) ≤ N * h := by
    dsimp [N]
    field_simp
    nlinarith
  refine ⟨N, hN, ?_⟩
  exact lt_of_le_of_lt (scaled_window_tail_le w hw h N hh hN n hscale) hn

/-- The numerical window/tail part of the conditional theta endpoint is
fulfilled by a rescaled actual normalized physical kernel. No smoothing
limits or Fourier representation are asserted. -/
theorem exists_concentrated_scaled_kernel (w : ℝ) (hw : 0 < w)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ N : ℝ, 0 < N ∧
      (∀ x : ℝ, 0 ≤ scaledTranslate w hw N (canonicalWindow δ / 2) x) ∧
      IntegrableOn (scaledTranslate w hw N (canonicalWindow δ / 2)) Set.univ volume ∧
      (1 - δ) * Real.exp (canonicalWindow δ) ≤
        (∫ x : ℝ in Set.Icc 0 (canonicalWindow δ), scaledTranslate w hw N (canonicalWindow δ / 2) x) ∧
      Real.exp (canonicalWindow δ) *
        (∫ x : ℝ in Set.Icc 0 (canonicalWindow δ), scaledTranslate w hw N (canonicalWindow δ / 2) x) ≤ 1 + δ ∧
      (∫ x : ℝ in (Set.Icc 0 (canonicalWindow δ))ᶜ, scaledTranslate w hw N (canonicalWindow δ / 2) x) ≤ δ := by
  obtain ⟨N, hN, ht⟩ := exists_scaled_window_small_tail w hw (canonicalWindow δ) (δ / 2)
    (canonicalWindow_pos δ hδ) (by linarith)
  have hki : IntegrableOn (scaledTranslate w hw N (canonicalWindow δ / 2)) Set.univ volume := by
    simpa only [integrableOn_univ] using scaledTranslate_integrable w hw N (canonicalWindow δ / 2) hN
  have hmass : (∫ x : ℝ in Set.univ, scaledTranslate w hw N (canonicalWindow δ / 2) x) = 1 := by
    simpa only [setIntegral_univ] using scaledTranslate_integral w hw N (canonicalWindow δ / 2) hN
  have hk : ∀ x : ℝ, 0 ≤ scaledTranslate w hw N (canonicalWindow δ / 2) x :=
    fun x => scaledTranslate_nonneg w hw N (canonicalWindow δ / 2) x hN
  have hb := canonicalWindow_bounds_of_tail δ hδ _ hk hki hmass (le_of_lt ht)
  exact ⟨N, hN, hk, hki, hb.1, hb.2.1, hb.2.2⟩

end HVRPhysicalKernelTailScaling
