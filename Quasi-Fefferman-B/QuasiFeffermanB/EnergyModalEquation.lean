import QuasiFeffermanB.EnergyGlobalLimit
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! Passage of the actual quadratic Fourier equation through energy-level
spacetime compactness. Only fixed Fourier coordinates are continuous in time;
no strong H0 continuity or regularity assumption is inserted. -/
set_option autoImplicit false
set_option Elab.async true
open Set MeasureTheory Filter
open scoped BigOperators Topology Interval ENNReal
namespace QuasiFeffermanB
open SingularClosure
noncomputable section

/-- Strong spacetime L2, the ordinary energy bound, and convergence of the
endpoint coordinates pass the actual Galerkin equation to every fixed mode. -/
theorem ENERGY_GALERKIN_MODAL_INTEGRAL
    (ν : ℝ) (hν : 0 ≤ ν) (a : ℕ → Field) (N : ℕ → ℕ)
    (g : ∀ n, GalerkinSolution ν (a n) (N n))
    (R T : ℝ) (hR : 0 ≤ R) (hT : 0 ≤ T)
    (hinit : ∀ n, coefficientEnergy (N n) ((g n).coeff 0) ≤ R ^ 2)
    (hexhaust : ∀ k : Frequency, k ≠ 0 → ∀ᶠ n in atTop, k ∈ cutoffModes (N n))
    (U : ℝ → TorusSobolev 0) (v : EnergyTimeH0L2 T)
    (hcoeff : ∀ t ∈ Icc (0 : ℝ) T, ∀ k i,
      Tendsto (fun n => (g n).coeff t k i) atTop (𝓝 ((U t).val k i)))
    (hv : Tendsto (fun n => (g n).energyTimeH0L2 T) atTop (𝓝 v))
    (hcompat : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T), v t = U t)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (k : Frequency) (i : Fin 3) :
    (U t).val k i = (U 0).val k i +
      ∫ r in (0 : ℝ)..t, fullFourierRhs ν (U r) k i := by
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, hT⟩
  by_cases hk : k = 0
  · subst k
    have hz (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) : (U s).val 0 i = 0 := by
      have hlim := hcoeff s hs 0 i
      have heq : (fun n => (g n).coeff s 0 i) = (fun _ : ℕ => (0 : ℂ)) := by
        funext n
        exact (g n).mode_support s hs.1 0 (cutoffModes_zero_not_mem _) i
      rw [heq] at hlim
      exact tendsto_nhds_unique hlim tendsto_const_nhds
    simp only [hz t ht, hz 0 hzero, fullFourierRhs_zero_frequency,
      intervalIntegral.integral_zero, add_zero]
  · obtain ⟨ψ, hψ, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hv).exists_seq_tendsto_ae
    have hcoe : ∀ᵐ r ∂volume.restrict (Icc (0 : ℝ) T), ∀ n : ℕ,
        (g n).energyTimeH0L2 T r = (g n).sobolevState 0 r := by
      rw [ae_all_iff]
      intro n
      exact ((g n).sobolevState_memLp 0 T 2).coeFn_toLp
    have hpointT : ∀ᵐ r ∂volume.restrict (Icc (0 : ℝ) T),
        Tendsto (fun n => fullFourierRhs ν ((g (ψ n)).sobolevState 0 r) k i)
          atTop (𝓝 (fullFourierRhs ν (U r) k i)) := by
      filter_upwards [hae, hcoe, hcompat] with r hr heq hrv
      have hactual : Tendsto (fun n => (g (ψ n)).sobolevState 0 r)
          atTop (𝓝 (U r)) := by
        have he : (fun n => (g (ψ n)).energyTimeH0L2 T r) =
            (fun n => (g (ψ n)).sobolevState 0 r) := by
          funext n
          exact heq (ψ n)
        simpa only [he, hrv] using hr
      exact ((fullFourierRhs_continuous ν k i).tendsto (U r)).comp hactual
    have hpoint := ae_restrict_of_ae_restrict_of_subset
      (Icc_subset_Icc le_rfl ht.2) hpointT
    have hmeas (n : ℕ) : AEStronglyMeasurable
        (fun r => fullFourierRhs ν ((g (ψ n)).sobolevState 0 r) k i)
        (volume.restrict (Icc (0 : ℝ) t)) := by
      apply ContinuousOn.aestronglyMeasurable_of_isCompact _ isCompact_Icc measurableSet_Icc
      exact (fullFourierRhs_continuous ν k i).comp_continuousOn
        (((g (ψ n)).sobolevState_continuousOn 0).mono (fun r hr => hr.1))
    have hbound (n : ℕ) : ∀ᵐ r ∂volume.restrict (Icc (0 : ℝ) t),
        ‖fullFourierRhs ν ((g (ψ n)).sobolevState 0 r) k i‖ ≤
          energyModeRhsBound ν R k i := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
      exact fullFourierRhs_energy_bound ν R hR _
        (galerkin_H0_energy_bound hν (g (ψ n)) R hR (hinit (ψ n)) r hr.1) k i
    have hint := tendsto_integral_of_dominated_convergence
      (μ := volume.restrict (Icc (0 : ℝ) t))
      (F := fun n r => fullFourierRhs ν ((g (ψ n)).sobolevState 0 r) k i)
      (f := fun r => fullFourierRhs ν (U r) k i)
      (fun _ => energyModeRhsBound ν R k i) hmeas (integrable_const _) hbound hpoint
    have hint' : Tendsto
        (fun n => ∫ r in (0 : ℝ)..t,
          fullFourierRhs ν ((g (ψ n)).sobolevState 0 r) k i)
        atTop (𝓝 (∫ r in (0 : ℝ)..t, fullFourierRhs ν (U r) k i)) := by
      simpa only [intervalIntegral.integral_of_le ht.1, integral_Icc_eq_integral_Ioc]
        using hint
    have heq : (fun n => ∫ r in (0 : ℝ)..t,
        fullFourierRhs ν ((g (ψ n)).sobolevState 0 r) k i) =ᶠ[atTop]
        (fun n => (g (ψ n)).coeff t k i - (g (ψ n)).coeff 0 k i) := by
      filter_upwards [hψ.tendsto_atTop.eventually (hexhaust k hk)] with n hn
      have h := (g (ψ n)).coefficient_integral_fullFourierRhs hn i le_rfl ht.1
      simpa only [(g (ψ n)).sobolevState_coeff 0 ht.1,
        (g (ψ n)).sobolevState_coeff 0 le_rfl] using h
    have hend := (hcoeff t ht k i).comp hψ.tendsto_atTop
    have hstart := (hcoeff 0 hzero k i).comp hψ.tendsto_atTop
    have hid : (∫ r in (0 : ℝ)..t, fullFourierRhs ν (U r) k i) =
        (U t).val k i - (U 0).val k i :=
      tendsto_nhds_unique hint' ((hend.sub hstart).congr' heq.symm)
    rw [hid]
    ring

end
end QuasiFeffermanB
