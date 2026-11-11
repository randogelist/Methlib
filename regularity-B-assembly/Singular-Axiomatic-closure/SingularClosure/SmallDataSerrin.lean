import SingularClosure.SmallDataQuantitative
import SingularClosure.CriticalSerrinTime

/-! The constructed quantitative solution satisfies the actual Serrin L4 L6
condition used in the physical weak-strong uniqueness estimate. -/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory
open scoped Interval

namespace SingularClosure
noncomputable section

theorem SMALL_DATA_CRITICAL_SERRIN_REGULARITY
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
            (4 * (ν - criticalNonlinearConstant * ‖a‖))) ∧
      (∀ T : ℝ, 0 < T →
        MemLp (fun t => criticalSpatialNorm 6 (U.flow.velocity t)) 4
          (volume.restrict (Ioc (0 : ℝ) T))) := by
  obtain ⟨U, hW, hV, hQ⟩ :=
    SMALL_DATA_CRITICAL_QUANTITATIVE_REGULARITY ν hν a ha hsmall
  exact ⟨U, hW, hV, hQ, fun T hT => U.serrin_time_memLp T (hQ T hT).1⟩

end
end SingularClosure
