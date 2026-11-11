import SingularClosure.CriticalUniformBounds
import SingularClosure.CriticalLimitRepresentatives
import SingularClosure.CriticalPositiveLimit
import SingularClosure.CriticalRegularityContracts

/-! Actual small critical-data existence. Every analytic construction is
provided by a theorem in the imported proof spine. External audit is required
before promotion of this candidate. -/
set_option autoImplicit false
set_option Elab.async true
open Set MeasureTheory Filter
open scoped Topology Interval
namespace SingularClosure
noncomputable section

/-- Smallness alone constructs the actual critical flow and strong initial trace. -/
theorem SMALL_DATA_CRITICAL_REGULARITY
    (ν : ℝ) (hν : 0 < ν) (a : CriticalSobolev 1) (ha : CriticalSigmaZero a)
    (hsmall : criticalNonlinearConstant * ‖a‖ < ν) :
    CriticalGlobalRegularity ν a := by
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
    obtain ⟨U, V, hU, hV, hUc, hVc, _hUb, _hVb⟩ := hrep T hT
    exact ⟨U, V, hU, hV, hUc, hVc⟩
  obtain ⟨L, hL⟩ := SMALL_DATA_POSITIVE_FLOW_OF_H0_LIMIT ν hν a ha.reality hsmall φ hφ g
    (fun t => criticalToTorusH0 1 (by norm_num) (u t)) hu (fun T _ => hconv T)
  refine ⟨{
    critical := u
    flow := L
    continuous := htrace.1
    initial := htrace.2
    coefficient_agreement := ?_
    critical_bound := hbound
    dissipation_uniform := ?_
  }⟩
  · intro t ht
    rw [hL t ht, criticalToTorusH0_coeff]
  · refine ⟨criticalDissipationBudget ν a, criticalDissipationBudget_nonneg a hsmall, ?_⟩
    intro T hT
    obtain ⟨U, _V, hU, _hV, hUc, _hVc, hUb, _hVb⟩ := hrep T hT
    exact ⟨U, hU, hUc, hUb⟩

/-- Exact scoped root: datumwise AX6 and actual regularity under the explicit
critical smallness condition. No universal AX6 hypothesis occurs. -/
theorem NSE_H12_SIGMA_ZERO_SMALL_REGULARITY
    (ν : ℝ) (hν : 0 < ν) (a : CriticalSobolev 1) (ha : CriticalSigmaZero a)
    (hsmall : criticalNonlinearConstant * ‖a‖ < ν) :
    CriticalDatumAX6 ν a ∧ CriticalGlobalRegularity ν a :=
  ⟨SMALL_DATA_AX6 ν hν a ha.reality ha.solenoidal ha.mean_zero hsmall,
    SMALL_DATA_CRITICAL_REGULARITY ν hν a ha hsmall⟩

/-- A viscosity-scaled ball of the full actual H1/2_sigma,0 space. -/
theorem NSE_H12_SIGMA_ZERO_SMALL_UNIVERSAL_CONSTANT :
    ∃ c : ℝ, 0 < c ∧ ∀ ν : ℝ, 0 < ν → ∀ a : CriticalSobolev 1,
      CriticalSigmaZero a → ‖a‖ < c * ν →
        CriticalDatumAX6 ν a ∧ CriticalGlobalRegularity ν a := by
  refine ⟨criticalNonlinearConstant⁻¹, inv_pos.mpr criticalNonlinearConstant_pos, ?_⟩
  intro ν hν a ha hsmall
  apply NSE_H12_SIGMA_ZERO_SMALL_REGULARITY ν hν a ha
  have h := mul_lt_mul_of_pos_left hsmall criticalNonlinearConstant_pos
  simpa only [← mul_assoc, mul_inv_cancel₀ criticalNonlinearConstant_pos.ne', one_mul] using h

end
end SingularClosure
