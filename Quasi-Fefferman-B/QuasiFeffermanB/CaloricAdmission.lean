import SingularClosure.CriticalPositiveFlow
import SingularClosure.CriticalSerrinUniqueness

/-!
All-Leray-Hopf identification with an actual positive-time Sobolev NSE flow.
The common physical trace and finite-horizon Serrin norm are explicit
quantitative hypotheses, not abstract uniqueness assumptions.
-/

set_option autoImplicit false
set_option Elab.async true

open Set Filter MeasureTheory
open scoped ContDiff ENNReal Topology Interval

namespace QuasiFeffermanB
open SingularClosure
noncomputable section

/-- The existing actual-PDE comparison on finite horizons identifies every
Leray-Hopf competitor at every positive time. -/
theorem POSITIVE_FLOW_LH_COMPARISON_OF_TRACE_AND_SERRIN
    (ν : ℝ) (hν : 0 < ν) (a₀ : CriticalPhysicalL2)
    (L : CriticalPositiveSobolevFlow ν)
    (htrace : Tendsto
      (fun t => eLpNorm (L.velocity t - (a₀ : Vec → Vec)) 2
        (volume.restrict unitCube)) (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hSerrin : ∀ T : ℝ, 0 < T →
      MemLp (fun t => criticalSpatialNorm 6 (L.velocity t)) 4
        (volume.restrict (Ioc (0 : ℝ) T)))
    (v : Velocity) (G : ℝ → Vec → (Vec →L[ℝ] Vec))
    (hv : CriticalLerayHopf ν a₀ v G) :
    ∀ t : ℝ, 0 < t → v t =ᵐ[volume.restrict unitCube] L.velocity t := by
  have hu : CriticalPositiveSolenoidalTest L.velocity := {
    smooth := L.velocity_spacetime_smooth
    periodic := fun t ht => (L.velocity_smoothSigmaZero t ht).periodic
    solenoidal := fun t ht => (L.velocity_smoothSigmaZero t ht).divergence_free
  }
  have hp (t : ℝ) (ht : 0 < t) : ContDiff ℝ ∞ (L.pressure t) :=
    fullTransportPressure_contDiff (L.state 0 t) (L.state_all_mem t ht)
      (L.reality t ht) (L.solenoidal t ht)
  intro t ht
  exact CRITICAL_LERAY_HOPF_SERRIN_COMPARISON_ON ν hν a₀ v L.velocity G L.pressure
    hv hu hp (fun r _ => fullTransportPressure_periodic (L.state 0 r))
    L.physical_equation htrace t ht (hSerrin t ht) t ⟨ht, le_rfl⟩

/-- Two actual LH trajectories with the same regular reference coincide as
physical L2 representatives, including the initial endpoint. -/
theorem TWO_LH_EQUAL_OF_POSITIVE_FLOW_TRACE_AND_SERRIN
    (ν : ℝ) (hν : 0 < ν) (a₀ : CriticalPhysicalL2)
    (L : CriticalPositiveSobolevFlow ν)
    (htrace : Tendsto
      (fun t => eLpNorm (L.velocity t - (a₀ : Vec → Vec)) 2
        (volume.restrict unitCube)) (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hSerrin : ∀ T : ℝ, 0 < T →
      MemLp (fun t => criticalSpatialNorm 6 (L.velocity t)) 4
        (volume.restrict (Ioc (0 : ℝ) T)))
    (v w : Velocity) (G H : ℝ → Vec → (Vec →L[ℝ] Vec))
    (hv : CriticalLerayHopf ν a₀ v G) (hw : CriticalLerayHopf ν a₀ w H) :
    ∀ t : ℝ, 0 ≤ t → v t =ᵐ[volume.restrict unitCube] w t := by
  intro t ht
  rcases eq_or_lt_of_le ht with hzero | hpos
  · subst t
    exact hv.initial.trans hw.initial.symm
  · exact (POSITIVE_FLOW_LH_COMPARISON_OF_TRACE_AND_SERRIN
      ν hν a₀ L htrace hSerrin v G hv t hpos).trans
        (POSITIVE_FLOW_LH_COMPARISON_OF_TRACE_AND_SERRIN
          ν hν a₀ L htrace hSerrin w H hw t hpos).symm

end
end QuasiFeffermanB
