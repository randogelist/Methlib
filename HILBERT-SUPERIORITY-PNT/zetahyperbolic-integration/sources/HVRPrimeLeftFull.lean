import HVRPrimeLeftIntegrable

/-! Candidate connection from the bounded interval kernel to the actual
full-line HVR kernel. The support condition is stated pointwise, and the
only limit proved here is the left finite-grid limit; the frequency-side
limit and PNT root integration are separate. External compilation, theorem
axiom audits and an integral-swap reachability trace remain required. -/

noncomputable section
open Filter MeasureTheory
open HVRPrimeDensityFubiniBridge HVRZetaHyperbolicFrequencyBounds
open HVRFrequencyWeightedCoefficients HVRPrimeLeftQuadrature
open HVRPrimeLeftIntegrable
open scoped BigOperators Topology

namespace HVRPrimeLeftFull

/-- Separation of the spatial and mode phases in the actual kernel. -/
theorem weighted_phase_eq_kernel_integrand (ψ : ℝ → ℂ) (x u t : ℝ) :
    weightedFrequency ψ x t * phase t u =
      ψ t * Complex.exp ((t : ℂ) * Complex.I * ((x - u : ℝ) : ℂ)) := by
  unfold weightedFrequency phase
  rw [mul_assoc, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The interval integral equals the actual full kernel when the test
vanishes off the interval. -/
theorem intervalKernel_eq_full_kernel (R : ℝ) (ψ : ℝ → ℂ) (x u : ℝ)
    (hsupport : ∀ t : ℝ, t ∉ Set.Ioc (-R) R → ψ t = 0) :
    intervalKernel R ψ x u = kernel ψ (x - u) := by
  unfold intervalKernel kernel
  have heq :
      (fun t : ℝ => weightedFrequency ψ x t * phase t u) =
        (fun t : ℝ => ψ t * Complex.exp ((t : ℂ) * Complex.I * ((x - u : ℝ) : ℂ))) := by
    funext t
    exact weighted_phase_eq_kernel_integrand ψ x u t
  rw [heq, ← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  filter_upwards [] with t
  by_cases ht : t ∈ Set.Ioc (-R) R
  · simp [ht]
  · simp [ht, hsupport t ht]

/-- The left quadrature converges to the actual HVR Abel-smoothed kernel
integral, assuming an explicit finite support interval for the test. -/
theorem left_integrals_tendsto_actual_kernel (R : ℝ) (ψ : ℝ → ℂ) (x a : ℝ)
    (hR : 0 ≤ R) (ha : 0 < a) (hψ : Integrable ψ)
    (hsupport : ∀ t : ℝ, t ∉ Set.Ioc (-R) R → ψ t = 0) :
    Tendsto (fun N : ℕ => ∫ u : ℝ in Set.Ioi 0,
      dampedError a u * sampleKernel R N ψ x u) atTop
      (𝓝 (∫ u : ℝ in Set.Ioi 0, dampedError a u * kernel ψ (x - u))) := by
  have h := left_integrals_tendsto_direct R ψ x a hR ha hψ
  simpa only [intervalKernel_eq_full_kernel R ψ x _ hsupport] using h

/-- The sampled kernel uses exactly the unit-frequency mixed modes from the
finite weighted-frequency identity. -/
theorem sampleKernel_mul_eq_weighted_modes
    (R : ℝ) (N : ℕ) (ψ : ℝ → ℂ) (x a u : ℝ) :
    dampedError a u * sampleKernel R N ψ x u =
      ∑ i ∈ Finset.range N,
        (∫ t : ℝ in HVRFrequencyIntervalCells.gridCell R N i,
          weightedFrequency ψ x t) *
        mixed (fun _ : ℝ => (1 : ℂ)) a 0 u
          (HVRFrequencyIntervalCells.gridPoint R N i) := by
  unfold sampleKernel
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_mul_const,
    HVRPrimeLaplaceFrequencyBounds.actual_mixed_eq_damped_phase]
  ring

/-- The exact left-limit premise used by the direct finite-frequency bridge,
for cell-integral coefficients and regular-grid sample frequencies. -/
theorem left_weighted_modes_tendsto_actual_kernel
    (R : ℝ) (ψ : ℝ → ℂ) (x a : ℝ)
    (hR : 0 ≤ R) (ha : 0 < a) (hψ : Integrable ψ)
    (hsupport : ∀ t : ℝ, t ∉ Set.Ioc (-R) R → ψ t = 0) :
    Tendsto (fun N : ℕ => ∫ u : ℝ in Set.Ioi 0,
      ∑ i ∈ Finset.range N,
        (∫ t : ℝ in HVRFrequencyIntervalCells.gridCell R N i,
          weightedFrequency ψ x t) *
        mixed (fun _ : ℝ => (1 : ℂ)) a 0 u
          (HVRFrequencyIntervalCells.gridPoint R N i)) atTop
      (𝓝 (∫ u : ℝ in Set.Ioi 0, dampedError a u * kernel ψ (x - u))) := by
  have h := left_integrals_tendsto_actual_kernel R ψ x a hR ha hψ hsupport
  simpa only [sampleKernel_mul_eq_weighted_modes] using h

end HVRPrimeLeftFull
