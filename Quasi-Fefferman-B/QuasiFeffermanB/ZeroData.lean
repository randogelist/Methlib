import QuasiFeffermanB.Cutoff
import QuasiFeffermanB.LHRestart

/-! The zero-datum branch of the frozen closed-cutoff statement. -/
set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory
open scoped ENNReal Topology

namespace QuasiFeffermanB
open SingularClosure
noncomputable section

theorem ZERO_LH_VELOCITY
    {ν : ℝ} (hν : 0 ≤ ν) {u : Velocity} {G : WeakGradientTrajectory}
    (hu : CriticalLerayHopf ν (0 : CriticalPhysicalL2) u G) :
    SameVelocity u (0 : Velocity) := by
  intro t ht
  have hL2 := hu.velocity_L2 t ht
  have hbound := hu.velocity_energy_le_initial hν ht
  simp only [norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] at hbound
  have hnorm : ‖criticalL2Representative (u t)‖ ^ 2 ≤ 0 := by
    rw [restart_representative_norm_sq (u t) hL2]
    exact hbound
  have hz : criticalL2Representative (u t) = 0 := by
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg (criticalL2Representative (u t))]
  have hrep : (criticalL2Representative (u t) : Field)
      =ᵐ[volume.restrict unitCube] u t := by
    rw [criticalL2Representative_eq _ hL2]
    exact hL2.coeFn_toLp
  have hrepzero : (criticalL2Representative (u t) : Field)
      =ᵐ[volume.restrict unitCube] (0 : Field) := by
    rw [hz]
    exact Lp.coeFn_zero Vec 2 (volume.restrict unitCube)
  exact hrep.symm.trans hrepzero

theorem ZERO_LH_SMOOTH_REPRESENTATIVE
    {ν : ℝ} (hν : 0 ≤ ν) {u : Velocity} {G : WeakGradientTrajectory}
    (hu : CriticalLerayHopf ν (0 : CriticalPhysicalL2) u G) :
    ∃ (v : Velocity) (p : Pressure),
      GlobalSmoothNSE ν (0 : Field) v p ∧ SameVelocity u v := by
  exact ⟨0, 0, globalSmoothNSE_zero ν, ZERO_LH_VELOCITY hν hu⟩

end
end QuasiFeffermanB
