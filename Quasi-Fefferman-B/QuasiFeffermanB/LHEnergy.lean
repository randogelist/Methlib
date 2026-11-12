import QuasiFeffermanB.Semantics

/-! Q02: the exact physical energy bounds for every standard LH trajectory. -/
set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory
open scoped Interval

namespace QuasiFeffermanB
open SingularClosure
noncomputable section

theorem LH_ENERGY_BOUNDS
    {ν : ℝ} {a : CriticalPhysicalL2} {u : Velocity}
    {G : WeakGradientTrajectory}
    (hν : 0 < ν) (hu : CriticalLerayHopf ν a u G) :
    (∀ t : ℝ, 0 ≤ t → physicalEnergy (u t) ≤ ‖a‖ ^ 2) ∧
    ∀ T : ℝ, 0 < T →
      IntervalIntegrable (fun t => criticalGradientEnergy (G t)) volume 0 T ∧
      (∫ t in (0 : ℝ)..T, criticalGradientEnergy (G t)) ≤ ‖a‖ ^ 2 / (2 * ν) := by
  constructor
  · intro t ht
    exact hu.velocity_energy_le_initial hν.le ht
  · intro T hT
    refine ⟨hu.dissipation_integrable T hT, ?_⟩
    have hE : 0 ≤ physicalEnergy (u T) := by
      rw [physicalEnergy_eq_integral_norm_sq]
      exact integral_nonneg (fun x => sq_nonneg _)
    have henergy := hu.energy_initial T hT.le
    apply (le_div_iff₀ (by positivity : 0 < 2 * ν)).2
    nlinarith

end
end QuasiFeffermanB
