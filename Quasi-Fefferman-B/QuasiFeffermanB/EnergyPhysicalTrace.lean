import QuasiFeffermanB.EnergyPeriodicRepresentative
import QuasiFeffermanB.EnergyWeakContinuity

/-! The exact physical initial datum and strong L2 trace of the energy-level
Fourier construction. The final representative is literally periodic. -/
set_option autoImplicit false
set_option Elab.async true
open Set MeasureTheory Filter
open scoped Topology ENNReal
namespace QuasiFeffermanB
open SingularClosure
noncomputable section

theorem energyPhysicalVelocityL2_initial (U : ℝ → TorusSobolev 0)
    (a : EnergyDatum) (hinit : (U 0).val = datumFourierCoeff (a.val : Field)) :
    energyPhysicalVelocityL2 U 0 = a.val := by
  apply physicalL2_fourier_injective
  rw [energyPhysicalVelocityL2, torusSobolevH0_physical_fourierCoeff _
    (by rw [hinit]; exact a.property.fourier_constraints.1)
    (by rw [hinit]; exact a.property.fourier_constraints.2.2), hinit]

theorem energyPeriodicVelocity_initial (U : ℝ → TorusSobolev 0)
    (a : EnergyDatum) (hinit : (U 0).val = datumFourierCoeff (a.val : Field)) :
    energyPeriodicVelocity U 0 =ᵐ[volume.restrict unitCube] (a.val : Field) := by
  have h := (energyPeriodicVelocity_ae U 0).symm
  simpa only [energyPhysicalVelocity, energyPhysicalVelocityL2_initial U a hinit] using h

theorem energyPhysical_initial_norm (U : ℝ → TorusSobolev 0)
    (a : EnergyDatum) (hinit : (U 0).val = datumFourierCoeff (a.val : Field)) :
    ‖U 0‖ = ‖a.val‖ := by
  have he := torusSobolevH0_physical_norm (U 0)
    (by rw [hinit]; exact a.property.fourier_constraints.1)
    (by rw [hinit]; exact a.property.fourier_constraints.2.2)
  change ‖energyPhysicalVelocityL2 U 0‖ = ‖U 0‖ at he
  rw [energyPhysicalVelocityL2_initial U a hinit] at he
  exact he.symm

theorem ENERGY_PHYSICAL_STRONG_INITIAL_TRACE
    (U : ℝ → TorusSobolev 0) (a : EnergyDatum)
    (hinit : (U 0).val = datumFourierCoeff (a.val : Field))
    (hbound : ∀ t, 0 ≤ t → ‖U t‖ ≤ ‖a.val‖)
    (hcoord : ∀ k i, ContinuousOn (fun t => (U t).val k i) (Ici 0)) :
    Tendsto (fun t => eLpNorm (energyPeriodicVelocity U t - (a.val : Field)) 2
      (volume.restrict unitCube)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hU := ENERGY_H0_STRONG_INITIAL_TRACE U
    (fun t ht => by rw [energyPhysical_initial_norm U a hinit]; exact hbound t ht)
    hcoord
  have hU' : Tendsto U (𝓝[>] (0 : ℝ)) (𝓝 (U 0)) :=
    hU.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
  have hphysical := (torusToPhysicalCubeL2.continuous.continuousAt.tendsto.comp
    (torusSobolevL2.continuous.continuousAt.tendsto.comp hU')).sub_const a.val
  have hnorm := hphysical.enorm
  have hinitial : torusToPhysicalCubeL2 (torusSobolevL2 (U 0)) = a.val :=
    energyPhysicalVelocityL2_initial U a hinit
  have hz : Tendsto (fun t => ‖energyPhysicalVelocityL2 U t - a.val‖ₑ)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [Function.comp_def, energyPhysicalVelocityL2, hinitial, sub_self,
      enorm_zero] using hnorm
  apply hz.congr'
  apply Filter.Eventually.of_forall
  intro t
  rw [Lp.enorm_def]
  apply eLpNorm_congr_ae
  exact (Lp.coeFn_sub _ _).trans
    ((energyPeriodicVelocity_ae U t).sub Filter.EventuallyEq.rfl)

end
end QuasiFeffermanB
