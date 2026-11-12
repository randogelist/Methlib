import QuasiFeffermanB.LHEnergy

/-! Exact frozen Q02, including the zero horizon. -/
set_option autoImplicit false
set_option Elab.async true
open Set MeasureTheory
open scoped Interval
namespace QuasiFeffermanB
open SingularClosure
noncomputable section

theorem Q02_LERAY_HOPF_ENERGY
    {ν : ℝ} {a : CriticalPhysicalL2} {u : Velocity}
    {G : WeakGradientTrajectory}
    (hν : 0 < ν) (hu : CriticalLerayHopf ν a u G) :
    (∀ t : ℝ, 0 ≤ t → physicalEnergy (u t) ≤ ‖a‖ ^ 2) ∧
    ∀ T : ℝ, 0 ≤ T →
      IntervalIntegrable (fun t => criticalGradientEnergy (G t)) volume 0 T ∧
      (∫ t in (0 : ℝ)..T, criticalGradientEnergy (G t)) ≤ ‖a‖ ^ 2 / (2 * ν) := by
  obtain ⟨hE, hD⟩ := LH_ENERGY_BOUNDS hν hu
  refine ⟨hE, ?_⟩
  intro T hT
  rcases eq_or_lt_of_le hT with hzero | hpos
  · subst T
    refine ⟨intervalIntegrable_refl, ?_⟩
    rw [intervalIntegral.integral_same]
    positivity
  · exact hD T hpos

end
end QuasiFeffermanB
