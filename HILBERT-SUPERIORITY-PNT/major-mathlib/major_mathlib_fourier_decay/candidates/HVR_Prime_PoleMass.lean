import HVR_Zeta_PoleResidue
import HVR_Correction_BoundaryLimit
import HVR_Prime_ResidueTransfer

noncomputable section

/-!
Candidate for the first required prime-series residue limit, along the
concrete sequence sigma_n = 1 + 1/(n+1). This depends on the actual zeta pole
limit and the actual holomorphic correction, and does not assume boundary
nonvanishing or PNT. External build and theorem-level audit are required.
-/
namespace HVRPrimePoleMass

open Filter HVRCorrectionBoundaryLimit HVRPrimeResidueTransfer
open HVRZetaPoleResidue HVRPrimeInfinite HVRPrimeZetaSplit
open HVRPowerCorrectionHolomorphic
open scoped Topology

theorem boundaryApproach_zero_ne_one (n : ℕ) :
    boundaryApproach 0 n ≠ (1 : ℂ) := by
  have hre : (boundaryApproach 0 n).re = 1 + boundaryEps n := by
    simp [boundaryApproach, zetaPoint]
  intro hz
  have hone : (boundaryApproach 0 n).re = 1 := by rw [hz]; norm_num
  have hp := boundaryEps_pos n
  linarith

theorem boundaryApproach_zero_sub_one (n : ℕ) :
    boundaryApproach 0 n - 1 = (boundaryEps n : ℂ) := by
  rw [boundaryApproach_eq]
  simp [boundaryPoint]

theorem boundaryApproach_zero_punctured :
    Tendsto (boundaryApproach 0) atTop (𝓝[≠] (1 : ℂ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · simpa only [boundaryPoint, Complex.ofReal_zero, zero_mul, add_zero] using
      boundaryApproach_tendsto 0
  · apply Filter.Eventually.of_forall
    intro n
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using
      boundaryApproach_zero_ne_one n

theorem normalized_zeta_pole_along_boundary :
    Tendsto (fun n : ℕ => (boundaryEps n : ℂ) *
      (-deriv riemannZeta (zetaPoint (1 + boundaryEps n) 0) /
        riemannZeta (zetaPoint (1 + boundaryEps n) 0)))
      atTop (𝓝 (1 : ℂ)) := by
  have h := normalized_zeta_logDerivative_tendsto_one.comp
    boundaryApproach_zero_punctured
  change Tendsto (fun n : ℕ => (boundaryApproach 0 n - 1) *
    (-deriv riemannZeta (boundaryApproach 0 n) / riemannZeta (boundaryApproach 0 n)))
      atTop (𝓝 (1 : ℂ)) at h
  simp only [boundaryApproach_zero_sub_one] at h
  simpa only [boundaryApproach] using h

/-- The normalized actual prime mass converges to 1 along sigma_n↓1. -/
theorem normalized_primeMass_pole_limit :
    Tendsto (fun n : ℕ => boundaryEps n * primeMass (1 + boundaryEps n))
      atTop (𝓝 (1 : ℝ)) := by
  have hc : Tendsto (fun n : ℕ => (boundaryEps n : ℂ) *
      complexCorrection (zetaPoint (1 + boundaryEps n) 0))
      atTop (𝓝 (0 : ℂ)) := by
    simpa only [boundaryApproach] using normalized_correction_tendsto_zero 0
  have h := primeMass_limit_of_log_derivative
    (fun n => 1 + boundaryEps n) boundaryEps (1 : ℂ)
    boundarySigma_gt_one normalized_zeta_pole_along_boundary hc
  simpa only [Complex.one_re] using h

end HVRPrimePoleMass
