import QuasiFeffermanB.LHExistence
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! The pointwise Fourier energy limit and the Bochner spacetime limit agree.
This identification uses actual Lp subsequence convergence and Fourier
coefficient injectivity, rather than an assumed compatibility certificate. -/
set_option autoImplicit false
set_option Elab.async true
open Set MeasureTheory Filter
open scoped Topology ENNReal Interval
namespace QuasiFeffermanB
open SingularClosure
noncomputable section

theorem energyGalerkinTimeLimits_compatible
    (ν : ℝ) (a : ℕ → Field) (N : ℕ → ℕ)
    (g : ∀ n, GalerkinSolution ν (a n) (N n)) (T : ℝ)
    (u : Icc (0 : ℝ) T → TorusSobolev 0) (v : EnergyTimeH0L2 T)
    (hc : ∀ k i, TendstoUniformly
      (fun n (t : Icc (0 : ℝ) T) => ((g n).sobolevState 0 t.val).val k i)
      (fun t => (u t).val k i) atTop)
    (hv : Tendsto (fun n => (g n).energyTimeH0L2 T) atTop (𝓝 v)) :
    ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T), ∀ ht : t ∈ Icc (0 : ℝ) T,
      v t = u ⟨t, ht⟩ := by
  obtain ⟨ψ, hψ, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hv).exists_seq_tendsto_ae
  have hcoe : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T), ∀ n : ℕ,
      (g n).energyTimeH0L2 T t = (g n).sobolevState 0 t := by
    rw [ae_all_iff]
    intro n
    exact ((g n).sobolevState_memLp 0 T 2).coeFn_toLp
  filter_upwards [hae, hcoe] with t htend hcoe
  intro ht
  have hactual : Tendsto (fun n => (g (ψ n)).sobolevState 0 t) atTop (𝓝 (v t)) := by
    have he : (fun n => (g (ψ n)).energyTimeH0L2 T t) =
        (fun n => (g (ψ n)).sobolevState 0 t) := by
      funext n
      exact hcoe (ψ n)
    simpa only [he] using htend
  apply Subtype.ext
  funext k i
  have hleft := ((torusSobolevH0Coeff_continuous k i).tendsto (v t)).comp hactual
  have hright := ((hc k i).tendsto_at ⟨t, ht⟩).comp hψ.tendsto_atTop
  exact tendsto_nhds_unique hleft hright

theorem ENERGY_GALERKIN_COMPATIBLE_L2H0_SUBSEQUENCE
    (ν : ℝ) (hν : 0 < ν) (a : ℕ → Field) (N : ℕ → ℕ)
    (g : ∀ n, GalerkinSolution ν (a n) (N n))
    (R T : ℝ) (hR : 0 ≤ R) (hT : 0 ≤ T)
    (hinit : ∀ n, coefficientEnergy (N n) ((g n).coeff 0) ≤ R ^ 2) :
    ∃ u : Icc (0 : ℝ) T → TorusSobolev 0, ∃ v : EnergyTimeH0L2 T,
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ (∀ t, ‖u t‖ ≤ R) ∧
      (∀ k i, TendstoUniformly
        (fun n (t : Icc (0 : ℝ) T) => ((g (φ n)).sobolevState 0 t.val).val k i)
        (fun t => (u t).val k i) atTop) ∧
      Tendsto (fun n => (g (φ n)).energyTimeH0L2 T) atTop (𝓝 v) ∧
      (∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T), ∀ ht : t ∈ Icc (0 : ℝ) T,
        v t = u ⟨t, ht⟩) := by
  obtain ⟨u, v, φ, hφ, hb, hc, hv⟩ :=
    ENERGY_GALERKIN_L2H0_SUBSEQUENCE ν hν a N g R T hR hT hinit
  exact ⟨u, v, φ, hφ, hb, hc, hv,
    energyGalerkinTimeLimits_compatible ν (fun n => a (φ n)) (fun n => N (φ n))
      (fun n => g (φ n)) T u v hc hv⟩

end
end QuasiFeffermanB

