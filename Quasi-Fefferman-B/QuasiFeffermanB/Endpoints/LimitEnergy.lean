import QuasiFeffermanB.EnergyGlobalLimit
import QuasiFeffermanB.EnergyLimitEnergy
import QuasiFeffermanB.EnergyPeriodicRepresentative
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Measure.Restrict

/-!
R4 endpoint extraction from the R2/R3 mathematical derivation.
Candidate source only: no local Lean execution and no new axiom-audit claim.
The original physical velocity and the single global gradient are retained.
The initial estimate uses the constant budget R². The interval estimate
selects its conull set of starting times before quantifying terminal times.
-/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal Interval

namespace QuasiFeffermanB
open SingularClosure
noncomputable section

private theorem endpoint_periodic_energy
    (U : ℝ → TorusSobolev 0) (t : ℝ)
    (hr : SpectralReality (U t).val)
    (hz : SpectralMeanZero (U t).val) :
    physicalEnergy (energyPeriodicVelocity U t) = ‖U t‖ ^ 2 := by
  let hv := energyPeriodicVelocity_memLp U t
  have hclass : hv.toLp (energyPeriodicVelocity U t) = energyPhysicalVelocityL2 U t :=
    (criticalL2Representative_eq (energyPeriodicVelocity U t) hv).symm.trans
      (energyPeriodicVelocity_L2 U t)
  rw [physicalEnergy_eq_toLp_norm_sq (energyPeriodicVelocity U t) hv, hclass]
  exact congrArg (fun r : ℝ => r ^ 2) (torusSobolevH0_physical_norm (U t) hr hz)

/-- Joint terminal/dissipation passage with the constant initial budget. -/
private theorem endpoint_initial_sobolev_budget
    (ν : ℝ) (hν : 0 < ν) (a : ℕ → Field) (N : ℕ → ℕ)
    (g : ∀ n, GalerkinSolution ν (a n) (N n)) (R : ℝ)
    (hinit : ∀ n, coefficientEnergy (N n) ((g n).coeff 0) ≤ R ^ 2)
    (U : ℝ → TorusSobolev 0) (W : ℝ → CriticalSobolev 2)
    (t : ℝ) (ht : 0 ≤ t)
    (hc : ∀ r, 0 ≤ r → ∀ k i,
      Tendsto (fun n => (g n).coeff r k i) atTop (𝓝 ((U r).val k i)))
    (hW : MemLp W 2 (volume.restrict (Icc (0 : ℝ) t)))
    (hw : ∀ᵐ r ∂volume.restrict (Icc (0 : ℝ) t),
      criticalCoeff 2 (W r) = (U r).val) :
    ‖U t‖ ^ 2 + 2 * ν * (∫ r in Icc (0 : ℝ) t, ‖W r‖ ^ 2) ≤ R ^ 2 := by
  let v : CriticalSobolev 0 := criticalH0Equiv.symm (U t)
  have hv : criticalCoeff 0 v = (U t).val := by
    calc
      criticalCoeff 0 v = (criticalH0Equiv v).val := (criticalH0Equiv_coeff v).symm
      _ = (U t).val := congrArg (fun z : TorusSobolev 0 => z.val)
        (criticalH0Equiv.apply_symm_apply (U t))
  have hcont (n : ℕ) : ContinuousOn ((g n).criticalState 2) (Icc (0 : ℝ) t) :=
    ((g n).criticalState_continuousOn 2).mono (fun r hr => hr.1)
  have hsq (n : ℕ) (r : ℝ) : ‖(g n).criticalState (2 : ℤ) r‖ ^ 2 =
      coefficientDissipation (N n) ((g n).coeff r) := by
    have hnat : ‖(g n).criticalState (2 : ℤ) r‖ ^ 2 =
        criticalEnergy (2 : ℕ) (N n) ((g n).coeff r) := by
      simpa only [Nat.cast_ofNat] using (g n).criticalState_norm_sq_nat 2 r
    exact hnat.trans
      (criticalEnergy_two_eq_coefficientDissipation (N n) ((g n).coeff r))
  have hpass := ENERGY_MODAL_INTERVAL_BUDGET_LIMIT
    (volume.restrict (Icc (0 : ℝ) t)) (2 * ν) (by positivity)
    (fun n => (g n).criticalState 0 t) v (fun n => (g n).criticalState 2) W
    (fun _ : ℕ => R ^ 2) (R ^ 2)
    (by
      intro k i
      have heq (n : ℕ) : criticalCoeff 0 ((g n).criticalState 0 t) = (g n).coeff t :=
        (g n).criticalState_coeff 0 ht
      simpa only [heq, hv] using hc t ht k i)
    (fun n => (hcont n).aestronglyMeasurable_of_isCompact isCompact_Icc measurableSet_Icc)
    (fun n => ((hcont n).norm.pow 2).integrableOn_compact isCompact_Icc)
    ((memLp_two_iff_integrable_sq_norm hW.aestronglyMeasurable).mp hW)
    (by
      filter_upwards [hw, ae_restrict_mem measurableSet_Icc] with r hr hmem
      intro k i
      have heq (n : ℕ) : criticalCoeff 2 ((g n).criticalState 2 r) = (g n).coeff r :=
        (g n).criticalState_coeff 2 hmem.1
      simpa only [heq, hr] using hc r hmem.1 k i)
    (by
      intro n
      rw [galerkin_critical_zero_norm_sq]
      simp_rw [hsq]
      have h := GALERKIN_INTERVAL_ENERGY_IDENTITY (g n) (s := 0) (t := t) le_rfl ht
      rw [intervalIntegral.integral_of_le ht, ← integral_Icc_eq_integral_Ioc] at h
      exact h.le.trans (hinit n))
    tendsto_const_nhds
  simpa only [v, criticalH0Equiv.symm.norm_map] using hpass

/-- Both physical energy inequalities for the single global limit.
No initial-energy convergence, smallness, restart, or LH record is an input. -/
theorem ENERGY_PERIODIC_LIMIT_ENERGY
    (ν : ℝ) (hν : 0 < ν) (a : ℕ → Field) (N : ℕ → ℕ)
    (g : ∀ n, GalerkinSolution ν (a n) (N n)) (R : ℝ)
    (hinit : ∀ n, coefficientEnergy (N n) ((g n).coeff 0) ≤ R ^ 2)
    (U : ℝ → TorusSobolev 0)
    (hcoord : ∀ k i, ContinuousOn (fun t => (U t).val k i) (Ici 0))
    (hc : ∀ r, 0 ≤ r → ∀ k i,
      Tendsto (fun n => (g n).coeff r k i) atTop (𝓝 ((U r).val k i)))
    (htime : ∀ T : ℝ, 0 ≤ T → ∃ z : EnergyTimeH0L2 T,
      Tendsto (fun n => (g n).energyTimeH0L2 T) atTop (𝓝 z) ∧
      (∀ᵐ r ∂volume.restrict (Icc (0 : ℝ) T), z r = U r)) :
    (∀ t : ℝ, 0 ≤ t →
      physicalEnergy (energyPeriodicVelocity U t) +
        2 * ν * (∫ r in (0 : ℝ)..t, criticalGradientEnergy (energyGlobalGradient U r))
          ≤ R ^ 2) ∧
    (∀ T : ℝ, 0 < T →
      ∀ᵐ s ∂volume.restrict (Ioc (0 : ℝ) T), ∀ t ∈ Icc s T,
        physicalEnergy (energyPeriodicVelocity U t) +
          2 * ν * (∫ r in s..t, criticalGradientEnergy (energyGlobalGradient U r))
            ≤ physicalEnergy (energyPeriodicVelocity U s)) := by
  classical
  have hspec (r : ℝ) (hr : 0 ≤ r) := energy_modal_limit_constraints ν a N g U hc r hr
  have henergy (r : ℝ) (hr : 0 ≤ r) :
      physicalEnergy (energyPeriodicVelocity U r) = ‖U r‖ ^ 2 :=
    endpoint_periodic_energy U r (hspec r hr).1 (hspec r hr).2.2
  constructor
  · intro t ht
    obtain ⟨W, hW, hw, _⟩ :=
      energy_modal_limit_H1_representative ν hν a N g R t ht hinit U hcoord hc
    have hr : ∀ᵐ r ∂volume.restrict (Icc (0 : ℝ) t), SpectralReality (U r).val := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
      exact (hspec r hr.1).1
    have hz : ∀ᵐ r ∂volume.restrict (Icc (0 : ℝ) t), SpectralMeanZero (U r).val := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
      exact (hspec r hr.1).2.2
    have hD := energyGlobalGradient_energy_ae U W
      (volume.restrict (Icc (0 : ℝ) t)) hr hz hw
    have hI : (∫ r in (0 : ℝ)..t, criticalGradientEnergy (energyGlobalGradient U r)) =
        ∫ r in Icc (0 : ℝ) t, ‖W r‖ ^ 2 := by
      rw [intervalIntegral.integral_of_le ht, ← integral_Icc_eq_integral_Ioc]
      exact integral_congr_ae hD
    rw [henergy t ht, hI]
    exact endpoint_initial_sobolev_budget ν hν a N g R hinit U W t ht hc hW hw
  · intro T hT
    obtain ⟨W, hW, hw, _⟩ :=
      energy_modal_limit_H1_representative ν hν a N g R T hT.le hinit U hcoord hc
    obtain ⟨z, hz, hcompat⟩ := htime T hT.le
    obtain ⟨ψ, hψ, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hz).exists_seq_tendsto_ae
    have hcoe : ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) T), ∀ n : ℕ,
        (g n).energyTimeH0L2 T s = (g n).sobolevState 0 s := by
      rw [ae_all_iff]
      intro n
      exact ((g n).sobolevState_memLp 0 T 2).coeFn_toLp
    apply ae_restrict_of_ae_restrict_of_subset
      (show Ioc (0 : ℝ) T ⊆ Icc (0 : ℝ) T from fun s hs => ⟨hs.1.le, hs.2⟩)
    filter_upwards [hae, hcoe, hcompat, ae_restrict_mem measurableSet_Icc]
      with s hsconv hscoe hscompat hsmem
    have hactual : Tendsto (fun n => (g (ψ n)).sobolevState 0 s)
        atTop (𝓝 (U s)) := by
      have heq : (fun n => (g (ψ n)).energyTimeH0L2 T s) =
          (fun n => (g (ψ n)).sobolevState 0 s) := by
        funext n
        exact hscoe (ψ n)
      simpa only [heq, hscompat] using hsconv
    have hstart : Tendsto
        (fun n => coefficientEnergy (N (ψ n)) ((g (ψ n)).coeff s))
        atTop (𝓝 (‖U s‖ ^ 2)) := by
      simpa only [galerkin_H0_norm_sq] using hactual.norm.pow 2
    intro t ht
    have hsubset : Icc s t ⊆ Icc (0 : ℝ) T :=
      fun r hr => ⟨hsmem.1.trans hr.1, hr.2.trans ht.2⟩
    have hWlocal : MemLp W 2 (volume.restrict (Icc s t)) :=
      MemLp.mono_measure (Measure.restrict_mono hsubset le_rfl) hW
    have hwlocal : ∀ᵐ r ∂volume.restrict (Icc s t),
        criticalCoeff 2 (W r) = (U r).val :=
      ae_restrict_of_ae_restrict_of_subset hsubset hw
    have hclocal : ∀ r ∈ Icc s t, ∀ k i,
        Tendsto (fun n => (g (ψ n)).coeff r k i) atTop (𝓝 ((U r).val k i)) := by
      intro r hr k i
      exact (hc r (hsmem.1.trans hr.1) k i).comp hψ.tendsto_atTop
    have hpass := ENERGY_GALERKIN_INTERVAL_LIMIT ν hν
      (fun n => a (ψ n)) (fun n => N (ψ n)) (fun n => g (ψ n))
      U W s t hsmem.1 ht.1 hclocal hWlocal hwlocal hstart
    have hr : ∀ᵐ r ∂volume.restrict (Icc s t), SpectralReality (U r).val := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
      exact (hspec r (hsmem.1.trans hr.1)).1
    have hz' : ∀ᵐ r ∂volume.restrict (Icc s t), SpectralMeanZero (U r).val := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
      exact (hspec r (hsmem.1.trans hr.1)).2.2
    have hD := energyGlobalGradient_energy_ae U W (volume.restrict (Icc s t)) hr hz' hwlocal
    have hI : (∫ r in s..t, criticalGradientEnergy (energyGlobalGradient U r)) =
        ∫ r in Icc s t, ‖W r‖ ^ 2 := by
      rw [intervalIntegral.integral_of_le ht.1, ← integral_Icc_eq_integral_Ioc]
      exact integral_congr_ae hD
    rw [henergy t (hsmem.1.trans ht.1), henergy s hsmem.1, hI]
    exact hpass

end
end QuasiFeffermanB
