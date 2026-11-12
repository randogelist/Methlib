import SingularClosure.SobolevTimeL2Compactness
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Agreement of the uniform H0 and strong time-L² H1 limits

A further subsequence converges almost everywhere in H1 by the actual Lp
convergence theorem. Continuous Sobolev inclusion and uniqueness of the
pointwise H0 limit identify both representatives on the finite time interval.
The final theorem discharges both convergence hypotheses by the constructed
canonical Galerkin subsequence.
-/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory Filter
open scoped Topology ENNReal

namespace SingularClosure

noncomputable section

theorem canonicalSobolevTimeLimits_compatible
    (ν : ℝ) (hν : 0 < ν) (a : Field) (ha : SmoothSigmaZero a) (T : ℝ)
    (φ : ℕ → ℕ) (u0 : C(Icc (0 : ℝ) T, TorusSobolev 0)) (u1 : TimeH1L2 T)
    (h0 : TendstoUniformly
      (fun n (t : Icc (0 : ℝ) T) =>
        (canonicalGalerkinSolution ν hν a ha (φ n + 1)).sobolevState 0 t.val) u0 atTop)
    (h1 : Tendsto (fun n => canonicalSobolevTimeH1L2 ν hν a ha T (φ n)) atTop (𝓝 u1)) :
    ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T), ∀ ht : t ∈ Icc (0 : ℝ) T,
      torusSobolevInclusion 0 (u1 t) = u0 ⟨t, ht⟩ := by
  obtain ⟨ψ, hψ, hae⟩ := (tendstoInMeasure_of_tendsto_Lp h1).exists_seq_tendsto_ae
  have hcoe : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T), ∀ n : ℕ,
      canonicalSobolevTimeH1L2 ν hν a ha T (φ n) t =
        (canonicalGalerkinSolution ν hν a ha (φ n + 1)).sobolevState 1 t := by
    rw [ae_all_iff]
    intro n
    exact ((canonicalGalerkinSolution ν hν a ha (φ n + 1)).sobolevState_memLp 1 T 2).coeFn_toLp
  filter_upwards [hae, hcoe] with t htend hcoe
  intro ht
  have hactual : Tendsto
      (fun n => (canonicalGalerkinSolution ν hν a ha (φ (ψ n) + 1)).sobolevState 1 t)
      atTop (𝓝 (u1 t)) := by
    have he : (fun n => canonicalSobolevTimeH1L2 ν hν a ha T (φ (ψ n)) t) =
        (fun n => (canonicalGalerkinSolution ν hν a ha (φ (ψ n) + 1)).sobolevState 1 t) := by
      funext n
      exact hcoe (ψ n)
    simpa only [he] using htend
  have hinclusion : Tendsto
      (fun n => torusSobolevInclusion 0
        ((canonicalGalerkinSolution ν hν a ha (φ (ψ n) + 1)).sobolevState 1 t))
      atTop (𝓝 (torusSobolevInclusion 0 (u1 t))) :=
    (torusSobolevInclusion 0).continuous.continuousAt.tendsto.comp hactual
  simp only [GalerkinSolution.sobolevState_inclusion] at hinclusion
  have hpoint := (h0.tendsto_at ⟨t, ht⟩).comp hψ.tendsto_atTop
  exact tendsto_nhds_unique hinclusion hpoint

/-- The two strong limits describe the same actual time-dependent Sobolev field. -/
theorem AX6_CANONICAL_GALERKIN_COMPATIBLE_LIMITS (hAX6 : AX6Statement)
    (ν : ℝ) (hν : 0 < ν) (a : Field) (ha : SmoothSigmaZero a)
    (T : ℝ) (hT : 0 < T) :
    ∃ u0 : C(Icc (0 : ℝ) T, TorusSobolev 0), ∃ u1 : TimeH1L2 T,
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        TendstoUniformly
          (fun n (t : Icc (0 : ℝ) T) =>
            (canonicalGalerkinSolution ν hν a ha (φ n + 1)).sobolevState 0 t.val)
          u0 atTop ∧
        Tendsto (fun n => canonicalSobolevTimeH1L2 ν hν a ha T (φ n)) atTop (𝓝 u1) ∧
        (∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T), ∀ ht : t ∈ Icc (0 : ℝ) T,
          torusSobolevInclusion 0 (u1 t) = u0 ⟨t, ht⟩) := by
  obtain ⟨u0, u1, φ, hφ, h0, h1⟩ :=
    AX6_CANONICAL_GALERKIN_H0_L2H1_SUBSEQUENCE hAX6 ν hν a ha T hT
  exact ⟨u0, u1, φ, hφ, h0, h1,
    canonicalSobolevTimeLimits_compatible ν hν a ha T φ u0 u1 h0 h1⟩

end

end SingularClosure
