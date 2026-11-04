import HVRPrimeGridIntegrability
import HVRFrequencyMeshLimit

/-!
Finite-grid approximation of the inner frequency integral on a bounded
interval, with an explicit first-moment error after integration in the
positive half-line. The two outer integrabilities are stated as hypotheses.
The connection from the interval kernel to the original full-line kernel,
and discharge of the outer integrabilities, are separate obligations.

Candidate only: external Lean 4.34.0-rc1 compilation, theorem-level axiom
audits, and a transitive integral-swap dependency trace are still required.
-/

noncomputable section
open Filter MeasureTheory
open HVRPrimeDensityFubiniBridge HVRZetaHyperbolicFrequencyBounds
open HVRFrequencyIntervalCells HVRFrequencyWeightedCoefficients
open scoped BigOperators Topology

namespace HVRPrimeLeftQuadrature

/-- Phase multiplication preserves L1 integrability in the frequency variable. -/
theorem phase_mul_integrable {μ : Measure ℝ} (φ : ℝ → ℂ) (u : ℝ)
    (hφ : Integrable φ μ) : Integrable (fun t : ℝ => φ t * phase t u) μ := by
  have hp : Continuous (fun t : ℝ => phase t u) := by
    unfold phase
    fun_prop
  have hmeas : AEStronglyMeasurable (fun t : ℝ => φ t * phase t u) μ :=
    hφ.aestronglyMeasurable.mul hp.measurable.aestronglyMeasurable
  apply Integrable.mono' hφ.norm hmeas
  filter_upwards [] with t
  have hnorm : ‖phase t u‖ = 1 := by
    simp [phase, Complex.norm_exp, Complex.mul_re, Complex.mul_im]
  simp only [norm_mul, hnorm, mul_one, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _), le_refl]

/-- The cells give exactly the half-open frequency interval. -/
theorem gridCells_eq_Ioc (R : ℝ) (N : ℕ) (hR : 0 ≤ R) (hN : 0 < N) :
    (⋃ i ∈ Finset.range N, gridCell R N i) = Set.Ioc (-R) R := by
  apply Set.Subset.antisymm
  · intro t ht
    rcases Set.mem_iUnion.mp ht with ⟨i, hi⟩
    rcases Set.mem_iUnion.mp hi with ⟨hi, ht⟩
    have hiN : i + 1 ≤ N := Nat.succ_le_iff.mpr (Finset.mem_range.mp hi)
    have hl := gridPoint_monotone R N hR (Nat.zero_le i)
    have hr := gridPoint_monotone R N hR hiN
    rw [gridPoint_zero] at hl
    rw [gridPoint_end R N hN] at hr
    change gridPoint R N i < t ∧ t ≤ gridPoint R N (i + 1) at ht
    exact ⟨lt_of_le_of_lt hl ht.1, le_trans ht.2 hr⟩
  · exact gridCells_cover R N hN

def intervalKernel (R : ℝ) (ψ : ℝ → ℂ) (x u : ℝ) : ℂ :=
  ∫ t : ℝ in Set.Ioc (-R) R, weightedFrequency ψ x t * phase t u

def sampleKernel (R : ℝ) (N : ℕ) (ψ : ℝ → ℂ) (x u : ℝ) : ℂ :=
  ∑ i ∈ Finset.range N,
    ∫ t : ℝ in gridCell R N i,
      weightedFrequency ψ x t * phase (gridPoint R N i) u

/-- Pointwise approximation of the actual weighted frequency integral. -/
theorem intervalKernel_sample_error (R : ℝ) (N : ℕ) (ψ : ℝ → ℂ)
    (x u : ℝ) (hR : 0 ≤ R) (hN : 0 < N) (hψ : Integrable ψ) :
    ‖intervalKernel R ψ x u - sampleKernel R N ψ x u‖ ≤
      ((2 * R / (N : ℝ)) * |u|) * ∫ t : ℝ, ‖ψ t‖ := by
  let φ : ℝ → ℂ := weightedFrequency ψ x
  have hφ : Integrable φ := weightedFrequency_integrable ψ x hψ
  have hfreq : Integrable (fun t : ℝ => φ t * phase t u) :=
    phase_mul_integrable φ u hφ
  have hf : ∀ i ∈ Finset.range N, IntegrableOn
      (fun t : ℝ => φ t * phase t u) (gridCell R N i) := by
    intro i hi
    exact hfreq.mono_measure Measure.restrict_le_self
  have hg : ∀ i ∈ Finset.range N, IntegrableOn
      (fun t : ℝ => φ t * phase (gridPoint R N i) u) (gridCell R N i) := by
    intro i hi
    exact (hφ.mono_measure Measure.restrict_le_self).mul_const _
  have hδ : 0 ≤ 2 * R / (N : ℝ) := by positivity
  have h := HVRFrequencyCellBudget.finite_cells_phase_error_of_disjoint
    (Finset.range N) (gridCell R N) φ (gridPoint R N) u (2 * R / (N : ℝ)) hδ hφ
    (fun i hi => gridCells_measurable R N i) (gridCells_pairwise_disjoint R N hR)
    hf hg (gridCells_close_ae R N)
  have hunion := integral_biUnion_finset
    (μ := volume) (f := fun t : ℝ => φ t * phase t u)
    (Finset.range N) (fun i hi => gridCells_measurable R N i)
    (gridCells_pairwise_disjoint R N hR) hf
  rw [gridCells_eq_Ioc R N hR hN] at hunion
  rw [Finset.sum_sub_distrib, ← hunion] at h
  simpa only [intervalKernel, sampleKernel, φ, norm_weightedFrequency] using h

/-- Quantitative left-hand quadrature error. Integrability of the two outer
integrands is explicit and remains to be discharged in an application. -/
theorem left_integral_error (R : ℝ) (N : ℕ) (ψ : ℝ → ℂ) (x a : ℝ)
    (hR : 0 ≤ R) (hN : 0 < N) (ha : 0 < a) (hψ : Integrable ψ)
    (hfull : IntegrableOn (fun u : ℝ => dampedError a u * intervalKernel R ψ x u)
      (Set.Ioi 0))
    (happrox : IntegrableOn (fun u : ℝ => dampedError a u * sampleKernel R N ψ x u)
      (Set.Ioi 0)) :
    ‖(∫ u : ℝ in Set.Ioi 0, dampedError a u * intervalKernel R ψ x u) -
      (∫ u : ℝ in Set.Ioi 0, dampedError a u * sampleKernel R N ψ x u)‖ ≤
      ((2 * R / (N : ℝ)) * ∫ t : ℝ, ‖ψ t‖) *
        ∫ u : ℝ in Set.Ioi 0, |u| * ‖dampedError a u‖ := by
  apply HVRNativeDominatedLimit.integral_error_le_weighted
    ((2 * R / (N : ℝ)) * ∫ t : ℝ, ‖ψ t‖) hfull happrox
    (HVRPrimeDirectFrequency.first_moment_integrable_direct a ha)
  filter_upwards [] with u
  calc
    ‖dampedError a u * intervalKernel R ψ x u -
        dampedError a u * sampleKernel R N ψ x u‖ =
        ‖dampedError a u‖ * ‖intervalKernel R ψ x u - sampleKernel R N ψ x u‖ := by
          rw [← mul_sub, norm_mul]
    _ ≤ ‖dampedError a u‖ *
        (((2 * R / (N : ℝ)) * |u|) * ∫ t : ℝ, ‖ψ t‖) :=
      mul_le_mul_of_nonneg_left (intervalKernel_sample_error R N ψ x u hR hN hψ)
        (norm_nonneg _)
    _ = ((2 * R / (N : ℝ)) * ∫ t : ℝ, ‖ψ t‖) *
        (|u| * ‖dampedError a u‖) := by ring

/-- The left finite-grid integrals converge to the interval-kernel integral
once their explicit outer integrability obligations are supplied. -/
theorem left_integrals_tendsto (R : ℝ) (ψ : ℝ → ℂ) (x a : ℝ)
    (hR : 0 ≤ R) (ha : 0 < a) (hψ : Integrable ψ)
    (hfull : IntegrableOn (fun u : ℝ => dampedError a u * intervalKernel R ψ x u)
      (Set.Ioi 0))
    (happrox : ∀ N : ℕ, 0 < N → IntegrableOn
      (fun u : ℝ => dampedError a u * sampleKernel R N ψ x u) (Set.Ioi 0)) :
    Tendsto (fun N : ℕ => ∫ u : ℝ in Set.Ioi 0,
      dampedError a u * sampleKernel R N ψ x u) atTop
      (𝓝 (∫ u : ℝ in Set.Ioi 0, dampedError a u * intervalKernel R ψ x u)) := by
  apply HVRFrequencyMeshLimit.tendsto_of_grid_error R
    ((∫ t : ℝ, ‖ψ t‖) * ∫ u : ℝ in Set.Ioi 0, |u| * ‖dampedError a u‖)
  intro N hN
  have h := left_integral_error R N ψ x a hR hN ha hψ hfull (happrox N hN)
  rw [norm_sub_rev]
  convert h using 1 <;> ring

end HVRPrimeLeftQuadrature
