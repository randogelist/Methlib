import QuasiFeffermanB.EnergyH1Realization
import QuasiFeffermanB.EnergyDatumGlobal

/-! A single physical velocity and weak-gradient representative for the
global energy-level Fourier limit. Local Bochner representatives are proved
to agree with this canonical representative almost everywhere. -/
set_option autoImplicit false
set_option Elab.async true
open Set MeasureTheory Filter
open scoped BigOperators Topology Interval ENNReal
namespace QuasiFeffermanB
open SingularClosure
noncomputable section

def energyPhysicalVelocityL2 (U : ℝ → TorusSobolev 0) (t : ℝ) : PhysicalCubeL2 :=
  torusToPhysicalCubeL2 (torusSobolevL2 (U t))

def energyPhysicalVelocity (U : ℝ → TorusSobolev 0) : Velocity :=
  fun t => (energyPhysicalVelocityL2 U t : Field)

def energyGlobalH1State (U : ℝ → TorusSobolev 0) (t : ℝ) : CriticalSobolev 2 := by
  classical
  exact if hm : Memℓp (criticalWeightedCoeff 2 (U t).val) 2 then
    criticalSobolevOfCoeff 2 (U t).val hm else 0

def energyGlobalGradientL2 (U : ℝ → TorusSobolev 0) (t : ℝ) : EnergyPhysicalGradientL2 :=
  energyPhysicalGradient (energyGlobalH1State U t)

def energyGlobalGradient (U : ℝ → TorusSobolev 0) :
    ℝ → Vec → (Vec →L[ℝ] Vec) := fun t => (energyGlobalGradientL2 U t : _)

theorem energyGlobalH1State_eq (U : ℝ → TorusSobolev 0) (t : ℝ)
    (w : CriticalSobolev 2) (hw : criticalCoeff 2 w = (U t).val) :
    energyGlobalH1State U t = w := by
  have hm : Memℓp (criticalWeightedCoeff 2 (U t).val) 2 := by
    rw [← hw]
    exact criticalCoeff_mem 2 w
  unfold energyGlobalH1State
  rw [dif_pos hm]
  apply criticalCoeff_injective 2
  rw [criticalSobolevOfCoeff_coeff, hw]

theorem energyGlobalH1State_ae_eq (U : ℝ → TorusSobolev 0)
    (W : ℝ → CriticalSobolev 2) (μ : Measure ℝ)
    (hw : ∀ᵐ t ∂μ, criticalCoeff 2 (W t) = (U t).val) :
    energyGlobalH1State U =ᵐ[μ] W := by
  filter_upwards [hw] with t ht
  exact energyGlobalH1State_eq U t (W t) ht

theorem energyGlobalH1State_memLp (U : ℝ → TorusSobolev 0)
    (W : ℝ → CriticalSobolev 2) (μ : Measure ℝ)
    (hW : MemLp W 2 μ)
    (hw : ∀ᵐ t ∂μ, criticalCoeff 2 (W t) = (U t).val) :
    MemLp (energyGlobalH1State U) 2 μ :=
  hW.congr (energyGlobalH1State_ae_eq U W μ hw).symm

theorem energyGlobalGradient_memLp (U : ℝ → TorusSobolev 0)
    (W : ℝ → CriticalSobolev 2) (μ : Measure ℝ)
    (hW : MemLp W 2 μ)
    (hw : ∀ᵐ t ∂μ, criticalCoeff 2 (W t) = (U t).val) :
    MemLp (energyGlobalGradientL2 U) 2 μ :=
  energyPhysicalGradient.comp_memLp' (energyGlobalH1State_memLp U W μ hW hw)

theorem energyPhysicalVelocity_eq_H1 (U : ℝ → TorusSobolev 0) (t : ℝ)
    (w : CriticalSobolev 2) (hw : criticalCoeff 2 w = (U t).val) :
    energyPhysicalVelocityL2 U t =
      zeroSobolevPhysicalL2 (criticalSobolevLower 0 2 (by norm_num) w) := by
  have heq : U t = criticalH0Equiv (criticalSobolevLower 0 2 (by norm_num) w) := by
    apply Subtype.ext
    rw [criticalH0Equiv_coeff, criticalSobolevLower_coeff, hw]
  simp only [energyPhysicalVelocityL2, zeroSobolevPhysicalL2, heq]

theorem energyGlobalPhysical_spatial_H1 (U : ℝ → TorusSobolev 0)
    (W : ℝ → CriticalSobolev 2) (μ : Measure ℝ)
    (hr : ∀ᵐ t ∂μ, SpectralReality (U t).val)
    (hz : ∀ᵐ t ∂μ, SpectralMeanZero (U t).val)
    (hw : ∀ᵐ t ∂μ, criticalCoeff 2 (W t) = (U t).val) :
    ∀ᵐ t ∂μ, CriticalPhysicalH1 (energyPhysicalVelocity U t) (energyGlobalGradient U t) := by
  filter_upwards [hr, hz, hw] with t hrt hzt hwt
  have hwr : SpectralReality (criticalCoeff 2 (W t)) := by rw [hwt]; exact hrt
  have hwz : SpectralMeanZero (criticalCoeff 2 (W t)) := by rw [hwt]; exact hzt
  have h := ENERGY_FOURIER_H1_PHYSICAL_REALIZATION (W t) hwr hwz
  simpa only [energyPhysicalVelocity, energyPhysicalVelocity_eq_H1 U t (W t) hwt,
    energyGlobalGradient, energyGlobalGradientL2, energyGlobalH1State_eq U t (W t) hwt]
    using h

theorem energyGlobalGradient_energy_ae (U : ℝ → TorusSobolev 0)
    (W : ℝ → CriticalSobolev 2) (μ : Measure ℝ)
    (hr : ∀ᵐ t ∂μ, SpectralReality (U t).val)
    (hz : ∀ᵐ t ∂μ, SpectralMeanZero (U t).val)
    (hw : ∀ᵐ t ∂μ, criticalCoeff 2 (W t) = (U t).val) :
    (fun t => criticalGradientEnergy (energyGlobalGradient U t)) =ᵐ[μ]
      (fun t => ‖W t‖ ^ 2) := by
  filter_upwards [hr, hz, hw] with t hrt hzt hwt
  change criticalGradientEnergy
    (energyPhysicalGradient (energyGlobalH1State U t) : Vec → (Vec →L[ℝ] Vec)) = _
  rw [energyGlobalH1State_eq U t (W t) hwt]
  exact energyPhysicalGradient_energy (W t) (by rw [hwt]; exact hrt)
    (by rw [hwt]; exact hzt)

theorem energyGlobalGradient_energy_integrable (U : ℝ → TorusSobolev 0)
    (W : ℝ → CriticalSobolev 2) (μ : Measure ℝ)
    (hW : MemLp W 2 μ)
    (hr : ∀ᵐ t ∂μ, SpectralReality (U t).val)
    (hz : ∀ᵐ t ∂μ, SpectralMeanZero (U t).val)
    (hw : ∀ᵐ t ∂μ, criticalCoeff 2 (W t) = (U t).val) :
    Integrable (fun t => criticalGradientEnergy (energyGlobalGradient U t)) μ := by
  exact ((memLp_two_iff_integrable_sq_norm hW.aestronglyMeasurable).mp hW).congr
    (energyGlobalGradient_energy_ae U W μ hr hz hw).symm

end
end QuasiFeffermanB
