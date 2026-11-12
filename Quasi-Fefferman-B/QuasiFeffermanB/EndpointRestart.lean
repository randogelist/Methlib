import QuasiFeffermanB.LHRestart
import QuasiFeffermanB.MeanPreservation

/-! Exact frozen Q05: one conull set of admissible physical H1 restart
states; the native shifted LH structure contains the strong right trace. -/
set_option autoImplicit false
set_option Elab.async true
open Set MeasureTheory
open scoped ENNReal Topology
namespace QuasiFeffermanB
open SingularClosure
noncomputable section

theorem Q05_GOOD_RESTART_SET
    {ν : ℝ} {a : CriticalPhysicalL2} {u : Velocity}
    {G : WeakGradientTrajectory}
    (hν : 0 < ν) (ha : EnergySigmaZero a)
    (hu : CriticalLerayHopf ν a u G) :
    ∃ R : Set ℝ, R ⊆ Ioi 0 ∧
      (∀ᵐ s ∂volume.restrict (Ioi (0 : ℝ)), s ∈ R) ∧
      ∀ s ∈ R,
        CriticalPhysicalH1 (u s) (G s) ∧
        EnergySigmaZero (criticalL2Representative (u s)) ∧
        CriticalLerayHopf ν (criticalL2Representative (u s))
          (Shift s u) (fun t => G (s + t)) := by
  let R : Set ℝ := {s | 0 < s ∧ CriticalPhysicalH1 (u s) (G s) ∧
    CriticalLerayHopf ν (criticalL2Representative (u s))
      (timeTranslate s u) (timeTranslate s G)}
  refine ⟨R, fun s hs => hs.1, ?_, ?_⟩
  · filter_upwards [LH_RESTART_AE hu hν.le,
      ae_restrict_mem measurableSet_Ioi] with s hs hspos
    exact ⟨hspos, hs⟩
  · intro s hs
    refine ⟨hs.2.1, LH_POSITIVE_TRACE_ENERGY_SIGMA_ZERO hu ha s hs.1, ?_⟩
    simpa only [Shift, timeTranslate, add_comm] using hs.2.2

end
end QuasiFeffermanB
