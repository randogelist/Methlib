import SingularClosure.CriticalLimitTimeL2
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! The uniform H0 and strong L2 H1 limits represent the same rough trajectory. -/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory Filter
open scoped Topology ENNReal Interval

namespace SingularClosure

noncomputable section

theorem criticalGalerkinTimeLimits_compatible
    (ν : ℝ) (a : ℕ → Field) (N : ℕ → ℕ)
    (g : ∀ n, GalerkinSolution ν (a n) (N n)) (T : ℝ)
    (u0 : Icc (0 : ℝ) T → TorusSobolev 0) (u1 : TimeH1L2 T)
    (h0 : TendstoUniformly (fun n (t : Icc (0 : ℝ) T) =>
      (g n).sobolevState 0 t.val) u0 atTop)
    (h1 : Tendsto (fun n => (g n).criticalTimeH1L2 T) atTop (𝓝 u1)) :
    ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T), ∀ ht : t ∈ Icc (0 : ℝ) T,
      torusSobolevInclusion 0 (u1 t) = u0 ⟨t, ht⟩ := by
  obtain ⟨ψ, hψ, hae⟩ := (tendstoInMeasure_of_tendsto_Lp h1).exists_seq_tendsto_ae
  have hcoe : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T), ∀ n : ℕ,
      (g n).criticalTimeH1L2 T t = (g n).sobolevState 1 t := by
    rw [ae_all_iff]
    intro n
    exact ((g n).sobolevState_memLp 1 T 2).coeFn_toLp
  filter_upwards [hae, hcoe] with t htend hcoe
  intro ht
  have hactual : Tendsto (fun n => (g (ψ n)).sobolevState 1 t) atTop (𝓝 (u1 t)) := by
    have he : (fun n => (g (ψ n)).criticalTimeH1L2 T t) =
        (fun n => (g (ψ n)).sobolevState 1 t) := by
      funext n
      exact hcoe (ψ n)
    simpa only [he] using htend
  have hinclusion : Tendsto
      (fun n => torusSobolevInclusion 0 ((g (ψ n)).sobolevState 1 t)) atTop
      (𝓝 (torusSobolevInclusion 0 (u1 t))) :=
    (torusSobolevInclusion 0).continuous.continuousAt.tendsto.comp hactual
  simp only [GalerkinSolution.sobolevState_inclusion] at hinclusion
  have hpoint := (h0.tendsto_at ⟨t, ht⟩).comp hψ.tendsto_atTop
  exact tendsto_nhds_unique hinclusion hpoint

/-- Both constructed strong limits identify one time-dependent field. -/
theorem CRITICAL_GALERKIN_COMPATIBLE_H0_L2H1_SUBSEQUENCE
    (ν : ℝ) (a : ℕ → Field) (N : ℕ → ℕ)
    (g : ∀ n, GalerkinSolution ν (a n) (N n))
    (T A B D : ℝ) (hT : 0 ≤ T) (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hstate : ∀ n t, t ∈ Icc (0 : ℝ) T → ‖(g n).criticalState 1 t‖ ≤ A)
    (hspace : ∀ n, (∫ t in (0 : ℝ)..T, ‖(g n).criticalState 3 t‖ ^ 2) ≤ B)
    (htime : ∀ n, (∫ t in (0 : ℝ)..T, ‖(g n).criticalRhs (-1) t‖ ^ 2) ≤ D) :
    ∃ u : Icc (0 : ℝ) T → CriticalSobolev 1, ∃ u1 : TimeH1L2 T, ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ (∀ t, ‖u t‖ ≤ A) ∧
      Continuous (fun t => criticalToTorusH0 1 (by norm_num) (u t)) ∧
      TendstoUniformly (fun n (t : Icc (0 : ℝ) T) => (g (φ n)).sobolevState 0 t.val)
        (fun t => criticalToTorusH0 1 (by norm_num) (u t)) atTop ∧
      Tendsto (fun n => (g (φ n)).criticalTimeH1L2 T) atTop (𝓝 u1) ∧
      (∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T), ∀ ht : t ∈ Icc (0 : ℝ) T,
        torusSobolevInclusion 0 (u1 t) = criticalToTorusH0 1 (by norm_num) (u ⟨t, ht⟩)) := by
  obtain ⟨u, u1, φ, hφ, hu, hcont, h0, h1⟩ :=
    CRITICAL_GALERKIN_H0_L2H1_SUBSEQUENCE ν a N g T A B D hT hA hB hD hstate hspace htime
  exact ⟨u, u1, φ, hφ, hu, hcont, h0, h1,
    criticalGalerkinTimeLimits_compatible ν (fun n => a (φ n)) (fun n => N (φ n))
      (fun n => g (φ n)) T (fun t => criticalToTorusH0 1 (by norm_num) (u t)) u1 h0 h1⟩

end

end SingularClosure
