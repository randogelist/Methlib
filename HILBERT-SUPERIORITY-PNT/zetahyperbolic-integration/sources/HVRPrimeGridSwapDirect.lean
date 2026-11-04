import HVRPrimeFiniteFrequencyDirect
import HVRPrimeLeftFull
import HVRPrimeRightCompactSupport

/-!
Candidate assembly of the two one-dimensional grid limits with the direct
finite-frequency identity. The support-interval theorem is narrower than
the general product-integrable Fubini theorem. This source has not been
compiled or audited and is not yet connected to the PNT root.
-/

noncomputable section
open Filter MeasureTheory
open scoped Topology
open HVRPrimeDensityFubiniBridge HVRPrimeDensityLaplace
open HVRFrequencyWeightedCoefficients HVRFrequencyIntervalCells

namespace HVRPrimeGridSwapDirect

/-- The actual prime-density smoothing identity for an integrable frequency
test with a supplied compact interval support. -/
theorem abel_smoothing_eq_frequency_integral_of_support_interval
    (ψ : ℝ → ℂ) (a x R : ℝ) (hR : 0 ≤ R) (ha : 0 < a)
    (hψ : Integrable ψ)
    (hsupport : ∀ t : ℝ, t ∉ Set.Ioc (-R) R → ψ t = 0) :
    (∫ u : ℝ in Set.Ioi 0, dampedError a u * kernel ψ (x - u)) =
      ∫ t : ℝ, (ψ t * Complex.exp ((t : ℂ) * Complex.I * (x : ℂ))) *
        primeDensityLaplace ((a : ℂ) + (t : ℂ) * Complex.I) := by
  apply HVRPrimeFiniteFrequencyDirect.identity_of_weighted_frequency_approximation
    ψ a x ha (fun N i => gridPoint R N i)
      (fun N i => ∫ t : ℝ in gridCell R N i, weightedFrequency ψ x t)
  · exact HVRPrimeLeftFull.left_weighted_modes_tendsto_actual_kernel
      R ψ x a hR ha hψ hsupport
  · have h := HVRPrimeRightQuadrature.sampledRightGrid_tendsto_full
      R ψ x a hR ha hψ (Filter.Eventually.of_forall hsupport)
    simpa only [HVRPrimeRightQuadrature.sampledRightGrid, weightedFrequency] using h

/-- Compact support supplies the common radius for both limits. -/
theorem abel_smoothing_eq_frequency_integral_of_compact_support
    (ψ : ℝ → ℂ) (a x : ℝ) (ha : 0 < a)
    (hψ : Integrable ψ) (hcompact : HasCompactSupport ψ) :
    (∫ u : ℝ in Set.Ioi 0, dampedError a u * kernel ψ (x - u)) =
      ∫ t : ℝ, (ψ t * Complex.exp ((t : ℂ) * Complex.I * (x : ℂ))) *
        primeDensityLaplace ((a : ℂ) + (t : ℂ) * Complex.I) := by
  obtain ⟨R, hR, hsupport⟩ :=
    HVRPrimeRightCompactSupport.exists_grid_support_radius ψ hcompact
  exact abel_smoothing_eq_frequency_integral_of_support_interval
    ψ a x R hR ha hψ hsupport

end HVRPrimeGridSwapDirect
