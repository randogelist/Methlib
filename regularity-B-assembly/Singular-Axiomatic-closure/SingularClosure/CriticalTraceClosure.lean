import SingularClosure.CriticalLimitRepresentatives
import SingularClosure.CriticalLimitGlobal

/-! Strong critical trace from the three actual Galerkin estimates. -/

set_option autoImplicit false

open Set MeasureTheory Filter
open scoped BigOperators Topology ENNReal Interval

namespace SingularClosure

noncomputable section

/-- The two actual Galerkin time-energy budgets discharge the trace representatives. -/
theorem CRITICAL_GALERKIN_GLOBAL_STRONG_TRACE_OF_BUDGETS
    (ν : ℝ) (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hzero : SpectralMeanZero (criticalCoeff 1 a))
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (g : ∀ n, GalerkinSolution ν
      (finiteSynthesis (φ n + 1) (criticalCoeff 1 a)) (φ n + 1))
    (u : ℝ → CriticalSobolev 1) (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hu : ContinuousOn (fun t => criticalToTorusH0 1 (by norm_num) (u t)) (Ici 0))
    (hconv : ∀ T : ℝ, 0 < T → TendstoUniformlyOn (fun n t => (g n).sobolevState 0 t)
      (fun t => criticalToTorusH0 1 (by norm_num) (u t)) atTop (Icc (0 : ℝ) T))
    (hspace : ∀ n T, 0 ≤ T → (∫ t in (0 : ℝ)..T, ‖(g n).criticalState 3 t‖ ^ 2) ≤ B)
    (htime : ∀ n T, 0 ≤ T → (∫ t in (0 : ℝ)..T, ‖(g n).criticalRhs (-1) t‖ ^ 2) ≤ D) :
    ContinuousOn u (Ici (0 : ℝ)) ∧ u 0 = a := by
  apply CRITICAL_GALERKIN_GLOBAL_STRONG_TRACE ν a hreal hzero φ hφ g u hu hconv
  intro T hT
  obtain ⟨U, V, hU, hV, hUc, hVc, _, _⟩ :=
    CRITICAL_GALERKIN_LOCAL_BOCHNER_REPRESENTATIVES ν
      (fun n => finiteSynthesis (φ n + 1) (criticalCoeff 1 a)) φ hφ g u T B D
      hT.le hB hD (hu.mono (fun t ht => ht.1)) (hconv T hT)
      (fun n => hspace n T hT.le) (fun n => htime n T hT.le)
  exact ⟨U, V, hU, hV, hUc, hVc⟩

/-- The actual bounded Galerkin family has one global strong Hhalf limit with
the prescribed rough initial datum. No compactness or trace witness is an input. -/
theorem CRITICAL_GALERKIN_GLOBAL_COMPACTNESS_WITH_STRONG_TRACE
    (ν : ℝ) (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hzero : SpectralMeanZero (criticalCoeff 1 a))
    (g : ∀ n : ℕ, GalerkinSolution ν
      (finiteSynthesis (n + 1) (criticalCoeff 1 a)) (n + 1))
    (A B D : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hstate : ∀ n t, 0 ≤ t → ‖(g n).criticalState 1 t‖ ≤ A)
    (hspace : ∀ n T, 0 ≤ T → (∫ t in (0 : ℝ)..T, ‖(g n).criticalState 3 t‖ ^ 2) ≤ B)
    (htime : ∀ n T, 0 ≤ T → (∫ t in (0 : ℝ)..T, ‖(g n).criticalRhs (-1) t‖ ^ 2) ≤ D) :
    ∃ u : ℝ → CriticalSobolev 1, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ContinuousOn u (Ici (0 : ℝ)) ∧ u 0 = a ∧
      (∀ t, 0 ≤ t → ‖u t‖ ≤ A) ∧
      (∀ T : ℝ, TendstoUniformlyOn (fun n t => (g (φ n)).sobolevState 0 t)
        (fun t => criticalToTorusH0 1 (by norm_num) (u t)) atTop (Icc (0 : ℝ) T)) := by
  obtain ⟨u, φ, hφ, hbound, hu, hconv, _⟩ :=
    CRITICAL_GALERKIN_GLOBAL_COMPACTNESS ν
      (fun n => finiteSynthesis (n + 1) (criticalCoeff 1 a)) (fun n => n + 1)
      g A B D hA hB hD hstate hspace htime
  have htrace := CRITICAL_GALERKIN_GLOBAL_STRONG_TRACE_OF_BUDGETS ν a hreal hzero φ hφ
    (fun n => g (φ n)) u B D hB hD hu (fun T _ => hconv T)
    (fun n T hT => hspace (φ n) T hT) (fun n T hT => htime (φ n) T hT)
  exact ⟨u, φ, hφ, htrace.1, htrace.2, hbound, hconv⟩

end

end SingularClosure
