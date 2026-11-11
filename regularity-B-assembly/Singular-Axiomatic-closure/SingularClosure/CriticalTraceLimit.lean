import SingularClosure.CriticalTrace
import SingularClosure.CriticalSpaces

/-!
# Strong trace from uniformly vanishing finite-band energies

A complete-space limit is constructed from the continuous finite projections.
The hypothesis controls only their actual squared differences. Continuity and
the initial trace of the limit are conclusions of the theorem.
-/

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace SingularClosure

noncomputable section

/-- Vanishing squared band bounds make the finite projections uniformly Cauchy. -/
theorem criticalTrace_uniformCauchy_of_band_energy
    {H : Type*} [NormedAddCommGroup H]
    (F : ℕ → ℝ → H) (d : ℕ → ℝ) (T : ℝ)
    (hd : Tendsto d atTop (𝓝 (0 : ℝ)))
    (hband : ∀ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, ∀ t ∈ Icc (0 : ℝ) T,
      ‖F m t - F n t‖ ^ 2 ≤ d N) :
    UniformCauchySeqOn F atTop (Icc (0 : ℝ) T) := by
  rw [Metric.uniformCauchySeqOn_iff]
  intro ε hε
  have hevent : ∀ᶠ N in atTop, d N < ε ^ 2 :=
    (tendsto_order.1 hd).2 _ (sq_pos_of_pos hε)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hevent
  refine ⟨N, ?_⟩
  intro m hm n hn t ht
  rw [dist_eq_norm]
  exact (sq_lt_sq₀ (norm_nonneg _) hε.le).mp
    ((hband N m hm n hn t ht).trans_lt (hN N le_rfl))

/-- Uniform limits of finite projections construct a continuous strong trace. -/
theorem CRITICAL_TRACE_EXISTS_OF_BAND_ENERGY
    {H : Type*} [NormedAddCommGroup H] [CompleteSpace H]
    (F : ℕ → ℝ → H) (d : ℕ → ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hF : ∀ n : ℕ, ContinuousOn (F n) (Icc (0 : ℝ) T))
    (hd : Tendsto d atTop (𝓝 (0 : ℝ)))
    (hband : ∀ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, ∀ t ∈ Icc (0 : ℝ) T,
      ‖F m t - F n t‖ ^ 2 ≤ d N)
    (a : H) (hinit : Tendsto (fun n => F n 0) atTop (𝓝 a)) :
    ∃ u : ℝ → H,
      ContinuousOn u (Icc (0 : ℝ) T) ∧
      TendstoUniformlyOn F u atTop (Icc (0 : ℝ) T) ∧ u 0 = a := by
  classical
  have hC := criticalTrace_uniformCauchy_of_band_energy F d T hd hband
  have hex : ∀ t : Icc (0 : ℝ) T, ∃ z : H,
      Tendsto (fun n => F n t.val) atTop (𝓝 z) := by
    intro t
    exact cauchySeq_tendsto_of_complete (hC.cauchySeq t.property)
  choose v hv using hex
  let u : ℝ → H := fun t => if ht : t ∈ Icc (0 : ℝ) T then v ⟨t, ht⟩ else 0
  have hpoint : ∀ t ∈ Icc (0 : ℝ) T,
      Tendsto (fun n => F n t) atTop (𝓝 (u t)) := by
    intro t ht
    simpa only [u, dif_pos ht] using hv ⟨t, ht⟩
  have hu := hC.tendstoUniformlyOn_of_tendsto hpoint
  refine ⟨u, ?_, hu, ?_⟩
  · exact hu.continuousOn (Filter.Eventually.of_forall hF)
  · exact tendsto_nhds_unique (hpoint 0 ⟨le_rfl, hT⟩) hinit

/-- The strong critical Sobolev trace uses the actual half-order Fourier space. -/
theorem CRITICAL_HHALF_TRACE_EXISTS_OF_BAND_ENERGY
    (F : ℕ → ℝ → CriticalSobolev 1) (d : ℕ → ℝ)
    {T : ℝ} (hT : 0 ≤ T)
    (hF : ∀ n : ℕ, ContinuousOn (F n) (Icc (0 : ℝ) T))
    (hd : Tendsto d atTop (𝓝 (0 : ℝ)))
    (hband : ∀ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, ∀ t ∈ Icc (0 : ℝ) T,
      ‖F m t - F n t‖ ^ 2 ≤ d N)
    (a : CriticalSobolev 1) (hinit : Tendsto (fun n => F n 0) atTop (𝓝 a)) :
    ∃ u : ℝ → CriticalSobolev 1,
      ContinuousOn u (Icc (0 : ℝ) T) ∧
      TendstoUniformlyOn F u atTop (Icc (0 : ℝ) T) ∧ u 0 = a :=
  CRITICAL_TRACE_EXISTS_OF_BAND_ENERGY F d hT hF hd hband a hinit

end

end SingularClosure
