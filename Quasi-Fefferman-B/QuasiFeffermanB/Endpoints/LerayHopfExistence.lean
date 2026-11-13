import QuasiFeffermanB.Endpoints.InitialCoefficients
import QuasiFeffermanB.Endpoints.PhysicalMomentum
import QuasiFeffermanB.Endpoints.LimitEnergy
import QuasiFeffermanB.EnergyPhysicalContinuity
import QuasiFeffermanB.EnergyPhysicalTrace
import Mathlib.MeasureTheory.Measure.Restrict

/-!
R4 deterministic physical Leray--Hopf assembly.
All eleven fields belong to the original CriticalLerayHopf structure.
The datum, single global coefficient trajectory, and single global gradient
are fixed throughout. Candidate source: external compilation and exact
axiom audits remain required. No Lean execution is performed locally.
-/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal Interval

namespace QuasiFeffermanB
open SingularClosure
noncomputable section

private theorem endpoint_gradient_representative
    (U : ℝ → TorusSobolev 0) (t : ℝ) :
    criticalL2Representative (energyGlobalGradient U t) = energyGlobalGradientL2 U t := by
  change criticalL2Representative
    (energyGlobalGradientL2 U t : Vec → (Vec →L[ℝ] Vec)) = energyGlobalGradientL2 U t
  rw [criticalL2Representative_eq _ (Lp.memLp (energyGlobalGradientL2 U t)),
    Lp.toLp_coeFn]

/-- Actual physical existence from every solenoidal, mean-zero physical L² datum. -/
theorem Q01_LERAY_HOPF_EXISTENCE
    (ν : ℝ) (hν : 0 < ν) (a : CriticalPhysicalL2) (ha : EnergySigmaZero a) :
    ∃ (u : Velocity) (G : WeakGradientTrajectory), CriticalLerayHopf ν a u G := by
  classical
  let A : EnergyDatum := ⟨a, ha⟩
  let aSeq : ℕ → Field := fun n =>
    finiteSynthesis (n + 1) (datumFourierCoeff (a : Field))
  let N : ℕ → ℕ := fun n => n + 1
  let g : ∀ n, GalerkinSolution ν (aSeq n) (N n) :=
    energyDatumGalerkinFamily ν hν.le A
  have hinitFamily (n : ℕ) :
      coefficientEnergy (N n) ((g n).coeff 0) ≤ ‖a‖ ^ 2 :=
    energyDatumGalerkinFamily_energy_initial ν hν.le A n
  obtain ⟨U, σ, hσ, hbound, hcoord, hcoeff, htime⟩ :=
    ENERGY_GALERKIN_GLOBAL_LIMIT ν hν aSeq N g ‖a‖ (norm_nonneg a) hinitFamily
  have hp (t : ℝ) (ht : 0 ≤ t) (k : Frequency) (i : Fin 3) :
      Tendsto (fun n => (g (σ n)).coeff t k i) atTop (𝓝 ((U t).val k i)) :=
    (hcoeff (t + 1) k i).tendsto_at ⟨ht, by linarith⟩
  have hinit : (U 0).val = datumFourierCoeff (a : Field) := by
    apply ENERGY_GALERKIN_LIMIT_INITIAL_COEFFICIENTS ν hν.le A σ hσ ((U 0).val)
    intro k i
    exact hp 0 le_rfl k i
  let b : ℕ → Field := fun n => aSeq (σ n)
  let M : ℕ → ℕ := fun n => σ n + 1
  let γ : ∀ n, GalerkinSolution ν (b n) (M n) := fun n => g (σ n)
  have hM : Tendsto M atTop atTop := by
    have hmono : StrictMono M := by
      intro m n hmn
      exact Nat.add_lt_add_right (hσ hmn) 1
    exact hmono.tendsto_atTop
  have hinitSub (n : ℕ) : coefficientEnergy (M n) ((γ n).coeff 0) ≤ ‖a‖ ^ 2 :=
    hinitFamily (σ n)
  have hspec (t : ℝ) (ht : 0 ≤ t) :=
    energy_modal_limit_constraints ν b M γ U hp t ht
  have hreal (T : ℝ) :
      ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T), SpectralReality (U t).val := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact (hspec t ht.1).1
  have hzero (T : ℝ) :
      ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T), SpectralMeanZero (U t).val := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact (hspec t ht.1).2.2
  have hH1 (T : ℝ) (hT : 0 ≤ T) :
      ∃ W : ℝ → CriticalSobolev 2,
        MemLp W 2 (volume.restrict (Icc (0 : ℝ) T)) ∧
        (∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T), criticalCoeff 2 (W t) = (U t).val) ∧
        (∫ t in Icc (0 : ℝ) T, ‖W t‖ ^ 2) ≤ ‖a‖ ^ 2 / (2 * ν) :=
    energy_modal_limit_H1_representative ν hν b M γ ‖a‖ T hT hinitSub U hcoord hp
  have hmomentum : CriticalIntegratedWeakMomentum ν (energyPeriodicVelocity U) :=
    ENERGY_GALERKIN_PHYSICAL_MOMENTUM ν hν.le b M γ ‖a‖ (norm_nonneg a)
      hinitSub U hM hp (fun T hT => htime T hT.le)
  have henergy := ENERGY_PERIODIC_LIMIT_ENERGY ν hν b M γ ‖a‖ hinitSub U hcoord hp htime
  refine ⟨energyPeriodicVelocity U, energyGlobalGradient U,
    { momentum := hmomentum
      velocity_L2 := fun t _ => energyPeriodicVelocity_memLp U t
      velocity_energy_class := ?_
      gradient_energy_class := ?_
      initial := energyPeriodicVelocity_initial U A hinit
      weak_continuity := fun φ hφ =>
        ENERGY_PERIODIC_WEAK_CONTINUITY U (Ici 0) ‖a‖ (norm_nonneg a)
          (fun t ht => hbound t ht) hcoord φ hφ
      strong_trace := ENERGY_PHYSICAL_STRONG_INITIAL_TRACE U A hinit hbound hcoord
      spatial_H1 := ?_
      dissipation_integrable := ?_
      energy_initial := henergy.1
      energy_intervals := henergy.2 }⟩
  · intro T hT
    obtain ⟨z, _, hcompat⟩ := htime T hT.le
    have hU2 : MemLp U 2 (volume.restrict (Icc (0 : ℝ) T)) :=
      (memLp_congr_ae hcompat).mp (Lp.memLp z)
    have hUtop : MemLp U ∞ (volume.restrict (Icc (0 : ℝ) T)) := by
      apply memLp_top_of_bound hU2.aestronglyMeasurable ‖a‖
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      exact hbound t ht.1
    have hphysical : MemLp (fun t => energyPhysicalVelocityL2 U t) ∞
        (volume.restrict (Icc (0 : ℝ) T)) := by
      simpa only [Function.comp_def, energyH0PhysicalMap_apply] using
        energyH0PhysicalMap.comp_memLp' hUtop
    have hclass : MemLp
        (fun t => criticalL2Representative (energyPeriodicVelocity U t)) ∞
        (volume.restrict (Icc (0 : ℝ) T)) := by
      simpa only [energyPeriodicVelocity_L2] using hphysical
    exact MemLp.mono_measure
      (Measure.restrict_mono
        (show Ioc (0 : ℝ) T ⊆ Icc (0 : ℝ) T from fun t ht => ⟨ht.1.le, ht.2⟩)
        le_rfl) hclass
  · intro T hT
    obtain ⟨W, hW, hw, _⟩ := hH1 T hT.le
    have hK := energyGlobalGradient_memLp U W
      (volume.restrict (Icc (0 : ℝ) T)) hW hw
    have hclass : MemLp
        (fun t => criticalL2Representative (energyGlobalGradient U t)) 2
        (volume.restrict (Icc (0 : ℝ) T)) := by
      simpa only [endpoint_gradient_representative] using hK
    exact MemLp.mono_measure
      (Measure.restrict_mono
        (show Ioc (0 : ℝ) T ⊆ Icc (0 : ℝ) T from fun t ht => ⟨ht.1.le, ht.2⟩)
        le_rfl) hclass
  · intro T hT
    obtain ⟨W, _, hw, _⟩ := hH1 T hT.le
    exact ae_restrict_of_ae_restrict_of_subset
      (show Ioc (0 : ℝ) T ⊆ Icc (0 : ℝ) T from fun t ht => ⟨ht.1.le, ht.2⟩)
      (energyPeriodicVelocity_spatial_H1 U W
        (volume.restrict (Icc (0 : ℝ) T)) (hreal T) (hzero T) hw)
  · intro T hT
    obtain ⟨W, hW, hw, _⟩ := hH1 T hT.le
    have hD := energyGlobalGradient_energy_integrable U W
      (volume.restrict (Icc (0 : ℝ) T)) hW (hreal T) (hzero T) hw
    have hDo : Integrable (fun t => criticalGradientEnergy (energyGlobalGradient U t))
        (volume.restrict (Ioc (0 : ℝ) T)) :=
      hD.mono_measure
        (Measure.restrict_mono
          (show Ioc (0 : ℝ) T ⊆ Icc (0 : ℝ) T from fun t ht => ⟨ht.1.le, ht.2⟩)
          le_rfl)
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le).mpr hDo

end
end QuasiFeffermanB
