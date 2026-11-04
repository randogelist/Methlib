import HVRPrimeGridIntegrability
import HVRFrequencyMeshLimit

/-!
Right-frequency quadrature from the audited direct finite-cell estimate.

This candidate identifies the finite cell sum with an actual interval integral
and proves convergence as the mesh goes to zero.  The full-line corollary has
an explicitly stated almost-everywhere support hypothesis.  It does not use
the two-variable integral swap, nor does it assert the left-hand limit or the
PNT root. External Lean compilation and theorem-level audit are pending.
-/

noncomputable section
open Filter MeasureTheory
open HVRPrimeDensityFubiniBridge HVRPrimeDensityLaplace
open HVRFrequencyIntervalCells HVRFrequencyWeightedCoefficients
open scoped BigOperators Topology

namespace HVRPrimeRightQuadrature

/-- The half-open cells are a genuine partition of the full grid interval. -/
theorem gridCells_union_eq_interval (R : ℝ) (N : ℕ) (hR : 0 ≤ R) (hN : 0 < N) :
    (⋃ i ∈ Finset.range N, gridCell R N i) = Set.Ioc (-R) R := by
  apply Set.Subset.antisymm
  · intro t ht
    rw [Set.mem_iUnion] at ht
    obtain ⟨i, hi⟩ := ht
    rw [Set.mem_iUnion] at hi
    obtain ⟨hi, hti⟩ := hi
    change gridPoint R N i < t ∧ t ≤ gridPoint R N (i + 1) at hti
    have hleft : -R ≤ gridPoint R N i := by
      simpa only [gridPoint_zero] using
        gridPoint_monotone R N hR (Nat.zero_le i)
    have hright : gridPoint R N (i + 1) ≤ R := by
      have hi' : i + 1 ≤ N := Nat.succ_le_of_lt (Finset.mem_range.mp hi)
      simpa only [gridPoint_end R N hN] using gridPoint_monotone R N hR hi'
    exact ⟨lt_of_le_of_lt hleft hti.1, le_trans hti.2 hright⟩
  · exact gridCells_cover R N hN

def sampledRightGrid (R : ℝ) (N : ℕ) (ψ : ℝ → ℂ) (x a : ℝ) : ℂ :=
  ∑ i ∈ Finset.range N,
    (∫ t : ℝ in gridCell R N i, weightedFrequency ψ x t) *
      primeDensityLaplace ((a : ℂ) + (gridPoint R N i : ℂ) * Complex.I)

/-- The coefficient-weighted prime-density samples converge to the actual
frequency integral on the grid interval. -/
theorem sampledRightGrid_tendsto_interval
    (R : ℝ) (ψ : ℝ → ℂ) (x a : ℝ)
    (hR : 0 ≤ R) (ha : 0 < a) (hψ : Integrable ψ) :
    Tendsto (fun N : ℕ => sampledRightGrid R N ψ x a) atTop
      (𝓝 (∫ t : ℝ in Set.Ioc (-R) R, weightedFrequency ψ x t *
        primeDensityLaplace ((a : ℂ) + (t : ℂ) * Complex.I))) := by
  let M : ℝ := ∫ u : ℝ in Set.Ioi 0, |u| * ‖dampedError a u‖
  let T : ℝ → ℂ := fun t => primeDensityLaplace ((a : ℂ) + (t : ℂ) * Complex.I)
  have hM : 0 ≤ M := by
    dsimp [M]
    exact integral_nonneg (fun u => mul_nonneg (abs_nonneg u) (norm_nonneg _))
  apply HVRFrequencyMeshLimit.tendsto_of_grid_error R
    (M * ∫ t : ℝ, ‖ψ t‖) (fun N => sampledRightGrid R N ψ x a)
    (∫ t : ℝ in Set.Ioc (-R) R, weightedFrequency ψ x t * T t)
  intro N hN
  have hδ : 0 ≤ 2 * R / (N : ℝ) := by positivity
  have hφ := weightedFrequency_integrable ψ x hψ
  have hf : ∀ i ∈ Finset.range N, IntegrableOn
      (fun t : ℝ => weightedFrequency ψ x t * T t) (gridCell R N i) := by
    intro i hi
    exact HVRPrimeGridIntegrability.weighted_lipschitz_integrable_on_cell
      (gridCell R N i) (weightedFrequency ψ x) T (gridPoint R N i)
      (2 * R / (N : ℝ)) M hδ hM
      (HVRPrimeGridIntegrability.primeDensity_frequency_continuous a ha)
      (fun t r => HVRPrimeDirectFrequency.primeDensity_frequency_lipschitz_direct a t r ha)
      hφ (gridCells_close_ae R N i hi)
  have hsum : (∑ i ∈ Finset.range N,
      ∫ t : ℝ in gridCell R N i, weightedFrequency ψ x t * T t) =
      ∫ t : ℝ in Set.Ioc (-R) R, weightedFrequency ψ x t * T t := by
    have h := integral_biUnion_finset (μ := volume)
      (f := fun t : ℝ => weightedFrequency ψ x t * T t)
      (Finset.range N) (fun i hi => gridCells_measurable R N i)
      (gridCells_pairwise_disjoint R N hR) hf
    rw [gridCells_union_eq_interval R N hR hN] at h
    exact h.symm
  have hsample : (∑ i ∈ Finset.range N,
      ∫ t : ℝ in gridCell R N i, weightedFrequency ψ x t * T (gridPoint R N i)) =
      sampledRightGrid R N ψ x a := by
    unfold sampledRightGrid
    apply Finset.sum_congr rfl
    intro i hi
    rw [integral_mul_const]
  have h := HVRPrimeGridIntegrability.actual_prime_grid_error_no_cell_integrability
    R N ψ x a hR ha hψ
  change ‖∑ i ∈ Finset.range N,
      ((∫ t : ℝ in gridCell R N i, weightedFrequency ψ x t * T t) -
       (∫ t : ℝ in gridCell R N i, weightedFrequency ψ x t * T (gridPoint R N i)))‖ ≤
      ((2 * R / (N : ℝ)) * M) * ∫ t : ℝ, ‖ψ t‖ at h
  rw [Finset.sum_sub_distrib, hsum, hsample, norm_sub_rev] at h
  simpa only [mul_assoc] using h

/-- If the frequency weight vanishes off the grid interval, the same samples
converge to the whole-line integral. -/
theorem sampledRightGrid_tendsto_full
    (R : ℝ) (ψ : ℝ → ℂ) (x a : ℝ)
    (hR : 0 ≤ R) (ha : 0 < a) (hψ : Integrable ψ)
    (hsupport : ∀ᵐ t : ℝ, t ∉ Set.Ioc (-R) R → ψ t = 0) :
    Tendsto (fun N : ℕ => sampledRightGrid R N ψ x a) atTop
      (𝓝 (∫ t : ℝ, weightedFrequency ψ x t *
        primeDensityLaplace ((a : ℂ) + (t : ℂ) * Complex.I))) := by
  have heq : (∫ t : ℝ in Set.Ioc (-R) R, weightedFrequency ψ x t *
      primeDensityLaplace ((a : ℂ) + (t : ℂ) * Complex.I)) =
      ∫ t : ℝ, weightedFrequency ψ x t *
        primeDensityLaplace ((a : ℂ) + (t : ℂ) * Complex.I) := by
    apply setIntegral_eq_integral_of_ae_compl_eq_zero
    filter_upwards [hsupport] with t ht hnot
    simp [weightedFrequency, ht hnot]
  rw [← heq]
  exact sampledRightGrid_tendsto_interval R ψ x a hR ha hψ

end HVRPrimeRightQuadrature
