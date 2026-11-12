import SingularClosure.CriticalLimitFatou
import SingularClosure.CriticalTraceGalerkin

/-! Actual state and derivative Bochner representatives of a rough Galerkin limit. -/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory Filter
open scoped BigOperators Topology Interval ENNReal

namespace SingularClosure

noncomputable section

theorem criticalGalerkinLimit_zero_mode
    (ν : ℝ) (a : ℕ → Field) (φ : ℕ → ℕ)
    (g : ∀ n, GalerkinSolution ν (a n) (φ n + 1))
    (u : ℝ → TorusSobolev 0) (T : ℝ)
    (hconv : TendstoUniformlyOn (fun n t => (g n).sobolevState 0 t)
      u atTop (Icc (0 : ℝ) T))
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : SpectralMeanZero (u t).val := by
  exact torusSobolevH0_zero_mode_of_tendsto (hconv.tendsto_at ht)
    (Filter.Eventually.of_forall (fun n => (g n).sobolevState_zero_mode 0 t ht.1))

/-- Every actual uniform H0 limit inherits its bounded time-integrated Sobolev order. -/
theorem criticalGalerkinLimit_state_memLp
    (ν : ℝ) (a : ℕ → Field) (φ : ℕ → ℕ)
    (g : ∀ n, GalerkinSolution ν (a n) (φ n + 1))
    (u : ℝ → TorusSobolev 0) (q : ℤ) (T B : ℝ) (hT : 0 ≤ T) (hB : 0 ≤ B)
    (hu : ContinuousOn u (Icc (0 : ℝ) T))
    (hconv : TendstoUniformlyOn (fun n t => (g n).sobolevState 0 t)
      u atTop (Icc (0 : ℝ) T))
    (hbudget : ∀ n, (∫ t in (0 : ℝ)..T, ‖(g n).criticalState q t‖ ^ 2) ≤ B) :
    ∃ U : ℝ → CriticalSobolev q,
      MemLp U 2 (volume.restrict (Icc (0 : ℝ) T)) ∧
      (∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T), criticalCoeff q (U t) = (u t).val) ∧
      (∫ t in Icc (0 : ℝ) T, ‖U t‖ ^ 2) ≤ B := by
  apply critical_memLp_realization_of_modal_limit q T B hT hB
    (fun n => (g n).criticalState q) (fun t => (u t).val)
  · intro n
    exact ((g n).criticalState_continuousOn q).mono (fun t ht => ht.1)
  · intro k i
    exact (torusSobolevH0Coeff_continuous k i).comp_continuousOn hu
  · intro t ht
    exact criticalGalerkinLimit_zero_mode ν a φ g u T hconv t ht
  · exact hbudget
  · intro t ht k i
    exact criticalGalerkinLimit_criticalState_coeff_tendsto ν a φ g u T hconv q t ht k i

/-- The actual modal RHS has an H^q/2-valued Bochner representative from its Galerkin budget. -/
theorem criticalGalerkinLimit_rhs_memLp
    (ν : ℝ) (a : ℕ → Field) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (g : ∀ n, GalerkinSolution ν (a n) (φ n + 1))
    (u : ℝ → TorusSobolev 0) (q : ℤ) (T B : ℝ) (hT : 0 ≤ T) (hB : 0 ≤ B)
    (hu : ContinuousOn u (Icc (0 : ℝ) T))
    (hconv : TendstoUniformlyOn (fun n t => (g n).sobolevState 0 t)
      u atTop (Icc (0 : ℝ) T))
    (hbudget : ∀ n, (∫ t in (0 : ℝ)..T, ‖(g n).criticalRhs q t‖ ^ 2) ≤ B) :
    ∃ V : ℝ → CriticalSobolev q,
      MemLp V 2 (volume.restrict (Icc (0 : ℝ) T)) ∧
      (∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T),
        criticalCoeff q (V t) = fullFourierRhs ν (u t)) ∧
      (∫ t in Icc (0 : ℝ) T, ‖V t‖ ^ 2) ≤ B := by
  apply critical_memLp_realization_of_modal_limit q T B hT hB
    (fun n => (g n).criticalRhs q) (fun t => fullFourierRhs ν (u t))
  · intro n
    exact ((g n).criticalRhs_continuousOn q).mono (fun t ht => ht.1)
  · intro k i
    exact (fullFourierRhs_continuous ν k i).comp_continuousOn hu
  · intro t ht i
    exact fullFourierRhs_zero_frequency ν (u t) i
  · exact hbudget
  · intro t ht k i
    exact criticalGalerkinLimit_criticalRhs_coeff_tendsto ν a φ hφ g u T hconv q t ht k i

/-- The critical state and RHS estimates discharge both local Bochner premises
of the Hilbert-triple strong-trace theorem. -/
theorem CRITICAL_GALERKIN_LOCAL_BOCHNER_REPRESENTATIVES
    (ν : ℝ) (a : ℕ → Field) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (g : ∀ n, GalerkinSolution ν (a n) (φ n + 1))
    (u : ℝ → CriticalSobolev 1) (T B D : ℝ)
    (hT : 0 ≤ T) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hu : ContinuousOn (fun t => criticalToTorusH0 1 (by norm_num) (u t)) (Icc (0 : ℝ) T))
    (hconv : TendstoUniformlyOn (fun n t => (g n).sobolevState 0 t)
      (fun t => criticalToTorusH0 1 (by norm_num) (u t)) atTop (Icc (0 : ℝ) T))
    (hspace : ∀ n, (∫ t in (0 : ℝ)..T, ‖(g n).criticalState 3 t‖ ^ 2) ≤ B)
    (htime : ∀ n, (∫ t in (0 : ℝ)..T, ‖(g n).criticalRhs (-1) t‖ ^ 2) ≤ D) :
    ∃ U : ℝ → CriticalSobolev 3, ∃ V : ℝ → CriticalSobolev (-1),
      MemLp U 2 (volume.restrict (Icc (0 : ℝ) T)) ∧
      MemLp V 2 (volume.restrict (Icc (0 : ℝ) T)) ∧
      (∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T),
        criticalCoeff 3 (U t) = criticalCoeff 1 (u t)) ∧
      (∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T),
        criticalCoeff (-1) (V t) = fullFourierRhs ν (criticalToTorusH0 1 (by norm_num) (u t))) ∧
      (∫ t in Icc (0 : ℝ) T, ‖U t‖ ^ 2) ≤ B ∧
      (∫ t in Icc (0 : ℝ) T, ‖V t‖ ^ 2) ≤ D := by
  obtain ⟨U, hU, hUc, hUb⟩ := criticalGalerkinLimit_state_memLp ν a φ g
    (fun t => criticalToTorusH0 1 (by norm_num) (u t)) 3 T B hT hB hu hconv hspace
  obtain ⟨V, hV, hVc, hVb⟩ := criticalGalerkinLimit_rhs_memLp ν a φ hφ g
    (fun t => criticalToTorusH0 1 (by norm_num) (u t)) (-1) T D hT hD hu hconv htime
  refine ⟨U, V, hU, hV, ?_, hVc, hUb, hVb⟩
  simpa only [criticalToTorusH0_coeff] using hUc

end

end SingularClosure
