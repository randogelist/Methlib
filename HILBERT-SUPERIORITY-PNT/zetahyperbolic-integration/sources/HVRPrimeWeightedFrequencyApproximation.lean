import HVRZetaHyperbolicFiniteFrequency

/-!
Candidate adapter for weighted frequency cells.

The quadrature coefficients already include the value of the actual frequency
test and the spatial phase. Thus the finite identity is instantiated with the
constant test 1 at x = 0. The two explicit convergence hypotheses are still
open; this file proves no existence of suitable quadratures and does not remove
the actual root's continuous Fubini step.

Source candidate only, not compiled or audited.
-/

noncomputable section
open Filter MeasureTheory
open scoped Topology
open HVRPrimeDensityFubiniBridge HVRPrimeDensityLaplace
open HVRZetaHyperbolicFiniteFrequency

namespace HVRPrimeWeightedFrequencyApproximation

/-- A finite weighted sum of the actual prime-density Laplace modes. -/
theorem weighted_finite_frequency_identity
    (S : Finset ℕ) (frequency : ℕ → ℝ) (coefficient : ℕ → ℂ)
    (a : ℝ) (ha : 0 < a) :
    (∫ u : ℝ in Set.Ioi 0,
      ∑ i ∈ S, coefficient i *
        mixed (fun _ : ℝ => (1 : ℂ)) a 0 u (frequency i)) =
      ∑ i ∈ S, coefficient i *
        primeDensityLaplace ((a : ℂ) + (frequency i : ℂ) * Complex.I) := by
  have h := actual_finite_frequency_identity S frequency coefficient
    (fun _ : ℝ => (1 : ℂ)) a 0 ha
  simpa using h

/-- The continuous identity, conditional on both weighted quadrature limits.

For compactly supported ψ one can seek coefficients given by cell integrals
of ψ(t) exp(i t x); their convergence is not asserted by this theorem.
-/
theorem actual_identity_of_weighted_frequency_approximation
    (ψ : ℝ → ℂ) (a x : ℝ) (ha : 0 < a)
    (frequency : ℕ → ℕ → ℝ) (coefficient : ℕ → ℕ → ℂ)
    (hleft : Tendsto
      (fun N : ℕ => ∫ u : ℝ in Set.Ioi 0, ∑ i ∈ Finset.range N,
        coefficient N i * mixed (fun _ : ℝ => (1 : ℂ)) a 0 u (frequency N i))
      atTop (𝓝 (∫ u : ℝ in Set.Ioi 0, dampedError a u * kernel ψ (x - u))))
    (hright : Tendsto
      (fun N : ℕ => ∑ i ∈ Finset.range N, coefficient N i *
        primeDensityLaplace ((a : ℂ) + (frequency N i : ℂ) * Complex.I))
      atTop (𝓝 (∫ t : ℝ,
        (ψ t * Complex.exp ((t : ℂ) * Complex.I * (x : ℂ))) *
          primeDensityLaplace ((a : ℂ) + (t : ℂ) * Complex.I)))) :
    (∫ u : ℝ in Set.Ioi 0, dampedError a u * kernel ψ (x - u)) =
      ∫ t : ℝ, (ψ t * Complex.exp ((t : ℂ) * Complex.I * (x : ℂ))) *
        primeDensityLaplace ((a : ℂ) + (t : ℂ) * Complex.I) := by
  have heq :
      (fun N : ℕ => ∫ u : ℝ in Set.Ioi 0, ∑ i ∈ Finset.range N,
        coefficient N i * mixed (fun _ : ℝ => (1 : ℂ)) a 0 u (frequency N i)) =
      (fun N : ℕ => ∑ i ∈ Finset.range N, coefficient N i *
        primeDensityLaplace ((a : ℂ) + (frequency N i : ℂ) * Complex.I)) := by
    funext N
    exact weighted_finite_frequency_identity (Finset.range N) (frequency N)
      (coefficient N) a ha
  rw [heq] at hleft
  exact tendsto_nhds_unique hleft hright

end HVRPrimeWeightedFrequencyApproximation

