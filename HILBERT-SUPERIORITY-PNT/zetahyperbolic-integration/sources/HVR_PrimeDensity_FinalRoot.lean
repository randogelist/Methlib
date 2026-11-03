import HVR_PrimeDensity_DecompositionEndpoint
import HVR_PrimeDensity_BackwardDecomposition

noncomputable section
open Filter MeasureTheory
open scoped Topology
open HVRPrimeDensityPNTConditional HVRPrimeDensityConcentratedSqueeze
open HVRPrimeDensityDecompositionEndpoint HVRPrimeDensityBackwardDecomposition
open HVRPhysicalKernelScaledTranslate HVRPhysicalKernelTailScaling HVRPhysicalKernelCanonicalWindow

/-!
CANDIDATE ONLY. The exact theta-ratio limit is assembled from the separately
staged backward-decomposition candidate and the conditional endpoint. There
are no explicit analytic premises in the root theorem below. This file and its
new upstream candidates have not been built or audited externally. No Lean
was executed locally. Mathlib/cache provenance and transitive route independence
are not yet verified. No unconditional PNT claim follows from this source.
-/
namespace HVRPrimeDensityFinalRoot

/-- Candidate discharge of the explicit decomposition premise. -/
theorem backwardDecomposition : BackwardDecomposition := by
  intro k hk x
  exact backward_eq_halfLine_add_error k hk x

/-- Candidate discharge of the complete kernel-and-smoothing premise of the
previously audited conditional theta theorem. -/
theorem actual_prime_concentrated_smoothing :
    ∀ δ : ℝ, 0 < δ → δ < 1 →
      ∃ (h : ℝ) (k : ℝ → ℝ),
        (∀ v : ℝ, 0 ≤ k v) ∧ IntegrableOn k Set.univ volume ∧
        (1 - δ) * Real.exp h ≤ (∫ v : ℝ in Set.Icc 0 h, k v) ∧
        Real.exp h * (∫ v : ℝ in Set.Icc 0 h, k v) ≤ 1 + δ ∧
        (∫ v : ℝ in (Set.Icc 0 h)ᶜ, k v) ≤ δ ∧
        Tendsto (forwardSmooth k) atTop (𝓝 1) ∧
        Tendsto (backwardSmooth k) atTop (𝓝 1) := by
  intro δ hδ hδ1
  have hw : (0 : ℝ) < 1 := by norm_num
  obtain ⟨N, hN, hnonneg, hki, hleft, hright, htail⟩ :=
    exists_concentrated_scaled_kernel 1 hw δ hδ
  have hlimits := scaled_smoothing_limits_of_backward_decomposition
    backwardDecomposition 1 hw N (canonicalWindow δ / 2) hN
  exact ⟨canonicalWindow δ, scaledTranslate 1 hw N (canonicalWindow δ / 2),
    hnonneg, hki, hleft, hright, htail, hlimits.1, hlimits.2⟩

/-- Candidate exact unconditional theta-ratio endpoint; its proof body and
all candidate dependencies require external Lean compilation and named audits. -/
theorem theta_ratio_tendsto_one :
    Tendsto (fun x : ℝ => Chebyshev.theta x / x) atTop (𝓝 1) :=
  theta_ratio_tendsto_one_of_concentrated_smoothing actual_prime_concentrated_smoothing

end HVRPrimeDensityFinalRoot
