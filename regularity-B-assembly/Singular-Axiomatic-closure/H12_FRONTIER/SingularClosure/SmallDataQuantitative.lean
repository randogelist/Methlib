import SingularClosure.CriticalPhysicalQuantitative
import SingularClosure.CriticalPositiveLimit
import SingularClosure.CriticalRegularityContracts

/-! One actual solution simultaneously realizes the strong critical trace,
the explicit H3/2 and time-derivative budgets, and the sharp physical quartic
gradient budget. No quantitative limit certificate is assumed. -/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory Filter
open scoped Topology Interval ENNReal

namespace SingularClosure
noncomputable section

theorem SMALL_DATA_CRITICAL_QUANTITATIVE_REGULARITY
    (ν : ℝ) (hν : 0 < ν) (a : CriticalSobolev 1) (ha : CriticalSigmaZero a)
    (hsmall : criticalNonlinearConstant * ‖a‖ < ν) :
    ∃ U : CriticalRegularSolution ν a,
      (∀ T : ℝ, 0 < T → ∃ W : ℝ → CriticalSobolev 3,
        MemLp W 2 (volume.restrict (Icc (0 : ℝ) T)) ∧
        (∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T),
          criticalCoeff 3 (W t) = criticalCoeff 1 (U.critical t)) ∧
        (∫ t in Icc (0 : ℝ) T, ‖W t‖ ^ 2) ≤ criticalDissipationBudget ν a) ∧
      (∀ T : ℝ, 0 < T → ∃ V : ℝ → CriticalSobolev (-1),
        MemLp V 2 (volume.restrict (Icc (0 : ℝ) T)) ∧
        (∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T),
          criticalCoeff (-1) (V t) = datumFourierCoeff (timeDerivative U.flow.velocity t)) ∧
        (∫ t in Icc (0 : ℝ) T, ‖V t‖ ^ 2) ≤ criticalTimeDerivativeBudget ν a) ∧
      (∀ T : ℝ, 0 < T →
        IntegrableOn (fun t => physicalDissipation (U.flow.velocity t) ^ 2)
          (Icc (0 : ℝ) T) volume ∧
        (∫ t in (0 : ℝ)..T, physicalDissipation (U.flow.velocity t) ^ 2) ≤
          (‖a‖ ^ 4 - ‖U.critical T‖ ^ 4) /
            (4 * (ν - criticalNonlinearConstant * ‖a‖))) := by
  obtain ⟨u, φ, hφ, hbound, hu, hconv, _hstrongH1⟩ :=
    SMALL_DATA_GALERKIN_GLOBAL_COMPACTNESS ν hν.le a ha.reality ha.solenoidal hsmall
  let g : ∀ n, GalerkinSolution ν
      (finiteSynthesis (φ n + 1) (criticalCoeff 1 a)) (φ n + 1) :=
    fun n => criticalDatumGalerkinFamily ν hν.le a ha.reality ha.solenoidal (φ n)
  have hrep (T : ℝ) (hT : 0 < T) :=
    CRITICAL_GALERKIN_LOCAL_BOCHNER_REPRESENTATIVES ν
      (fun n => finiteSynthesis (φ n + 1) (criticalCoeff 1 a)) φ hφ g u T
      (criticalDissipationBudget ν a) (criticalTimeDerivativeBudget ν a)
      hT.le (criticalDissipationBudget_nonneg a hsmall)
      (criticalTimeDerivativeBudget_nonneg a hsmall)
      (hu.mono (fun t ht => ht.1)) (hconv T)
      (fun n => criticalGalerkin_state_three_integral_bound a ha.reality hsmall hT.le (g n))
      (fun n => CRITICAL_GALERKIN_TIME_DERIVATIVE_BUDGET hν.le a ha.reality hsmall hT.le (g n))
  have htrace : ContinuousOn u (Ici (0 : ℝ)) ∧ u 0 = a := by
    apply CRITICAL_GALERKIN_GLOBAL_STRONG_TRACE ν a ha.reality ha.mean_zero φ hφ g u hu
      (fun T _ => hconv T)
    intro T hT
    obtain ⟨W, V, hW, hV, hWc, hVc, _hWb, _hVb⟩ := hrep T hT
    exact ⟨W, V, hW, hV, hWc, hVc⟩
  obtain ⟨L, hL⟩ := SMALL_DATA_POSITIVE_FLOW_OF_H0_LIMIT ν hν a ha.reality hsmall φ hφ g
    (fun t => criticalToTorusH0 1 (by norm_num) (u t)) hu (fun T _ => hconv T)
  have hLc (t : ℝ) (ht : 0 < t) : (L.state 0 t).val = criticalCoeff 1 (u t) := by
    rw [hL t ht, criticalToTorusH0_coeff]
  let U : CriticalRegularSolution ν a := {
    critical := u
    flow := L
    continuous := htrace.1
    initial := htrace.2
    coefficient_agreement := hLc
    critical_bound := hbound
    dissipation_uniform := by
      refine ⟨criticalDissipationBudget ν a, criticalDissipationBudget_nonneg a hsmall, ?_⟩
      intro T hT
      obtain ⟨W, _V, hW, _hV, hWc, _hVc, hWb, _hVb⟩ := hrep T hT
      exact ⟨W, hW, hWc, hWb⟩
  }
  refine ⟨U, ?_, ?_, ?_⟩
  · intro T hT
    obtain ⟨W, _V, hW, _hV, hWc, _hVc, hWb, _hVb⟩ := hrep T hT
    exact ⟨W, hW, hWc, hWb⟩
  · intro T hT
    exact SMALL_DATA_LIMIT_PHYSICAL_NEGATIVE_HALF ν hν.le a ha.reality hsmall
      φ hφ g u L hLc T hT.le (hu.mono (fun t ht => ht.1)) (hconv T)
  · intro T hT
    exact SMALL_DATA_LIMIT_PHYSICAL_SHARP_QUARTIC ν a ha.reality hsmall
      φ g u L hLc T hT.le (hu.mono (fun t ht => ht.1)) (hconv T)

end
end SingularClosure
