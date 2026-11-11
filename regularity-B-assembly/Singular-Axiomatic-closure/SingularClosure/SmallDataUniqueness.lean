import SingularClosure.SmallDataSerrin
import SingularClosure.CriticalCubeL2
import SingularClosure.CriticalSerrinUniqueness

/-! Actual weak-strong uniqueness for the constructed critical small-data flow. -/
set_option autoImplicit false
set_option Elab.async true
open Set MeasureTheory Filter
open scoped ContDiff ENNReal Topology
namespace SingularClosure
noncomputable section

def CriticalRegularSolution.lerayHopfUnique
    {ν : ℝ} {a : CriticalSobolev 1} (U : CriticalRegularSolution ν a) : Prop :=
  ∀ (v : Velocity) (G : ℝ → Vec → (Vec →L[ℝ] Vec)),
    CriticalLerayHopf ν (criticalInitialPhysicalL2 a) v G →
      ∀ t : ℝ, 0 < t → v t =ᵐ[volume.restrict unitCube] U.flow.velocity t

theorem CriticalRegularSolution.lerayHopfUnique_of_serrin
    {ν : ℝ} {a : CriticalSobolev 1} (U : CriticalRegularSolution ν a) (hν : 0 < ν)
    (hSerrin : ∀ T : ℝ, 0 < T →
      MemLp (fun t => criticalSpatialNorm 6 (U.flow.velocity t)) 4
        (volume.restrict (Ioc (0 : ℝ) T))) :
    U.lerayHopfUnique := by
  intro v G hv t ht
  have hu : CriticalPositiveSolenoidalTest U.flow.velocity := {
    smooth := U.flow.velocity_spacetime_smooth
    periodic := fun r hr => (U.flow.velocity_smoothSigmaZero r hr).periodic
    solenoidal := fun r hr => (U.flow.velocity_smoothSigmaZero r hr).divergence_free
  }
  have hp (r : ℝ) (hr : 0 < r) : ContDiff ℝ ∞ (U.flow.pressure r) := by
    rw [← contDiffOn_univ]
    exact U.flow.pressure_spacetime_smooth.comp
      (contDiff_const.prodMk contDiff_id).contDiffOn (fun x _ => hr)
  exact CRITICAL_LERAY_HOPF_SERRIN_COMPARISON_ON ν hν (criticalInitialPhysicalL2 a)
    v U.flow.velocity G U.flow.pressure hv hu hp
    (fun r _ => fullTransportPressure_periodic (U.flow.state 0 r))
    U.flow.physical_equation U.physical_eLpNorm_initial_trace t ht (hSerrin t ht) t ⟨ht, le_rfl⟩

/-- No Serrin certificate is assumed: it is constructed from the critical datum. -/
theorem SMALL_DATA_CRITICAL_LERAY_HOPF_COMPARISON
    (ν : ℝ) (hν : 0 < ν) (a : CriticalSobolev 1) (ha : CriticalSigmaZero a)
    (hsmall : criticalNonlinearConstant * ‖a‖ < ν) :
    CriticalDatumAX6 ν a ∧ ∃ U : CriticalRegularSolution ν a,
      U.lerayHopfUnique ∧
      (∀ T : ℝ, 0 < T →
        MemLp (fun t => criticalSpatialNorm 6 (U.flow.velocity t)) 4
          (volume.restrict (Ioc (0 : ℝ) T))) := by
  obtain ⟨U, _hW, _hV, _hQ, hSerrin⟩ :=
    SMALL_DATA_CRITICAL_SERRIN_REGULARITY ν hν a ha hsmall
  exact ⟨SMALL_DATA_AX6 ν hν a ha.reality ha.solenoidal ha.mean_zero hsmall,
    U, U.lerayHopfUnique_of_serrin hν hSerrin, hSerrin⟩

end
end SingularClosure
