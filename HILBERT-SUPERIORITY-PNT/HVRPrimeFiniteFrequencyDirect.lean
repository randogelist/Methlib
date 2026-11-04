import HVRPrimeDirectFrequency
import HVRZetaHyperbolicFiniteFrequency

/-!
Direct finite-frequency bridge for the actual HVR prime-density Laplace line.

This module uses the directly proved one-variable mode integrability in
`HVRPrimeDirectFrequency`, rather than the older prime-density integrability
proof. It does not prove either continuous-frequency approximation limit.
The conditional adapter has the same finite expressions as
`HVRPrimeWeightedFrequencyApproximation` but uses the direct finite identity.
No local Lean compilation or external audit has yet been performed for this
source; axiom and transitive-dependency audits are required.
-/

noncomputable section
open Filter MeasureTheory
open scoped Topology
open HVRPrimeDensityFubiniBridge HVRPrimeDensityLaplace
open HVRZetaHyperbolicFrequencyBounds

namespace HVRPrimeFiniteFrequencyDirect

/-- The actual mixed term with constant frequency weight is integrable using
only the direct one-variable damped-phase bound. -/
theorem actual_unit_mixed_integrable (a t : ℝ) (ha : 0 < a) :
    IntegrableOn (fun u : ℝ => mixed (fun _ : ℝ => (1 : ℂ)) a 0 u t)
      (Set.Ioi 0) volume := by
  simpa only [HVRPrimeLaplaceFrequencyBounds.actual_mixed_eq_damped_phase] using
    (HVRPrimeDirectFrequency.damped_phase_integrable_direct a t ha)

/-- The finite weighted identity, with every frequency mode integrated using
the direct proof. No continuous-frequency interchange is used here. -/
theorem weighted_finite_identity
    (S : Finset ℕ) (frequency : ℕ → ℝ) (coefficient : ℕ → ℂ)
    (a : ℝ) (ha : 0 < a) :
    (∫ u : ℝ in Set.Ioi 0,
      ∑ i ∈ S, coefficient i *
        mixed (fun _ : ℝ => (1 : ℂ)) a 0 u (frequency i)) =
      ∑ i ∈ S, coefficient i *
        primeDensityLaplace ((a : ℂ) + (frequency i : ℂ) * Complex.I) := by
  rw [integral_finsetSum S
    (fun i _ => (actual_unit_mixed_integrable a (frequency i) ha).const_mul
      (coefficient i))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_const_mul]
  have h := HVRZetaHyperbolicFiniteFrequency.actual_fixed_frequency
    (fun _ : ℝ => (1 : ℂ)) a 0 (frequency i)
  simpa using congrArg (fun z : ℂ => coefficient i * z) h

/-- Conditional continuous-frequency identity. Both limits remain explicit,
and this statement alone does not close the continuous integral swap. -/
theorem identity_of_weighted_frequency_approximation
    (ψ : ℝ → ℂ) (a x : ℝ) (ha : 0 < a)
    (frequency : ℕ → ℕ → ℝ) (coefficient : ℕ → ℕ → ℂ)
    (hleft : Tendsto
      (fun N : ℕ => ∫ u : ℝ in Set.Ioi 0, ∑ i ∈ Finset.range N,
        coefficient N i * mixed (fun _ : ℝ => (1 : ℂ)) a 0 u (frequency N i))
      atTop (𝓝 (∫ u : ℝ in Set.Ioi 0, dampedError a u * kernel ψ (x - u))))
    (hright : Tendsto
      (fun N : ℕ => ∑ i ∈ Finset.range N, coefficient N i *
        primeDensityLaplace ((a : ℂ) + (frequency N i : ℝ) * Complex.I))
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
        primeDensityLaplace ((a : ℂ) + (frequency N i : ℝ) * Complex.I)) := by
    funext N
    exact weighted_finite_identity (Finset.range N) (frequency N) (coefficient N) a ha
  rw [heq] at hleft
  exact tendsto_nhds_unique hleft hright

end HVRPrimeFiniteFrequencyDirect
