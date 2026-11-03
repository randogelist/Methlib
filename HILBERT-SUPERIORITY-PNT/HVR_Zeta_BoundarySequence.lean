import HVR_Analytic_Residue
import HVR_Zeta_BoundaryFactor
import HVR_Correction_BoundaryLimit
import HVR_Prime_ResidueTransfer

noncomputable section

/-! Candidate local-to-sequence bridge for actual zeta boundary residues.
No zeta boundary nonvanishing or PNT is assumed. The generic residue and
all declarations here require an external Lean build and axiom audit. -/
namespace HVRZetaBoundarySequence

open Filter HVRAnalyticResidue HVRZetaBoundaryFactor
open HVRCorrectionBoundaryLimit HVRPrimeResidueTransfer HVRPrimeZetaSplit
open HVRPowerCorrectionHolomorphic HVRPrimeInfinite
open scoped Topology

theorem boundaryPoint_re (t : ℝ) : (boundaryPoint t).re = 1 := by
  simp [boundaryPoint]

theorem boundaryPoint_ne_one (t : ℝ) (ht : t ≠ 0) :
    boundaryPoint t ≠ (1 : ℂ) := by
  intro h
  have hi := congrArg Complex.im h
  apply ht
  simpa [boundaryPoint] using hi

theorem boundaryApproach_ne_center (t : ℝ) (n : ℕ) :
    boundaryApproach t n ≠ boundaryPoint t := by
  intro h
  have hr := congrArg Complex.re h
  rw [boundaryApproach_eq] at hr
  simp only [Complex.add_re, Complex.ofReal_re] at hr
  have heps := boundaryEps_pos n
  linarith

theorem boundaryApproach_sub_center (t : ℝ) (n : ℕ) :
    boundaryApproach t n - boundaryPoint t = (boundaryEps n : ℂ) := by
  rw [boundaryApproach_eq]
  ring

theorem boundaryApproach_punctured (t : ℝ) :
    Tendsto (boundaryApproach t) atTop (𝓝[≠] (boundaryPoint t)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · exact boundaryApproach_tendsto t
  · apply Filter.Eventually.of_forall
    intro n
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using
      boundaryApproach_ne_center t n

/-- The actual normalized negative log derivative at a regular boundary
point tends to minus its finite analytic order. -/
theorem zeta_boundary_neg_logderiv_residue (t : ℝ) (ht : t ≠ 0) :
    Tendsto (fun z : ℂ => (z - boundaryPoint t) *
      (-deriv riemannZeta z / riemannZeta z))
      (𝓝[≠] (boundaryPoint t))
      (𝓝 (-(analyticOrderNatAt riemannZeta (boundaryPoint t) : ℂ))) := by
  obtain ⟨g, hg, hgn, hfac⟩ := zeta_boundary_local_factor
    (boundaryPoint t) (boundaryPoint_re t) (boundaryPoint_ne_one t ht)
  exact normalized_neg_logDeriv_tendsto riemannZeta g (boundaryPoint t)
    (analyticOrderNatAt riemannZeta (boundaryPoint t)) hg hgn hfac

theorem zeta_boundary_neg_logderiv_sequence (t : ℝ) (ht : t ≠ 0) :
    Tendsto (fun n : ℕ => (boundaryEps n : ℂ) *
      (-deriv riemannZeta (zetaPoint (1 + boundaryEps n) t) /
        riemannZeta (zetaPoint (1 + boundaryEps n) t))) atTop
      (𝓝 (-(analyticOrderNatAt riemannZeta (boundaryPoint t) : ℂ))) := by
  have h := (zeta_boundary_neg_logderiv_residue t ht).comp
    (boundaryApproach_punctured t)
  change Tendsto (fun n : ℕ => (boundaryApproach t n - boundaryPoint t) *
    (-deriv riemannZeta (boundaryApproach t n) /
      riemannZeta (boundaryApproach t n))) atTop
      (𝓝 (-(analyticOrderNatAt riemannZeta (boundaryPoint t) : ℂ))) at h
  simp only [boundaryApproach_sub_center] at h
  simpa only [boundaryApproach] using h

/-- The actual prime cosine moment has the corresponding negative order
limit for a nonzero boundary ordinate. -/
theorem cosMoment_boundary_order_limit (t frequency : ℝ)
    (ht : frequency * t ≠ 0) :
    Tendsto (fun n : ℕ => boundaryEps n *
      cosMoment (1 + boundaryEps n) t frequency) atTop
      (𝓝 (-(analyticOrderNatAt riemannZeta (boundaryPoint (frequency * t)) : ℝ))) := by
  have hc : Tendsto (fun n : ℕ => (boundaryEps n : ℂ) *
      complexCorrection (zetaPoint (1 + boundaryEps n) (frequency * t)))
      atTop (𝓝 (0 : ℂ)) := by
    simpa only [boundaryApproach] using normalized_correction_tendsto_zero (frequency * t)
  have h := cosMoment_limit_of_log_derivative (fun n => 1 + boundaryEps n)
    boundaryEps t frequency
    (-(analyticOrderNatAt riemannZeta (boundaryPoint (frequency * t)) : ℂ))
    boundarySigma_gt_one (zeta_boundary_neg_logderiv_sequence (frequency * t) ht) hc
  simpa only [Complex.neg_re, Complex.natCast_re] using h

end HVRZetaBoundarySequence
