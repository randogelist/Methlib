import HVR_Prime_PoleMass
import HVR_Zeta_BoundaryFactor

noncomputable section

/-!
Conditional composition of the audited pole-mass limit, correction
continuity, residue transfer, actual zeta boundary factorization and the
prime Gram contradiction. The asserted zeta logarithmic-derivative limits
at nonzero ordinates are explicit hypotheses, not proved here. No PNT or
unconditional boundary nonvanishing is claimed. External Lean compilation
and theorem-level axiom audit are required.
-/
namespace HVRZetaGramResidueConditional

open Filter HVRCorrectionBoundaryLimit HVRPrimeResidueTransfer
open HVRPrimePoleMass HVRPrimeBoundaryBridge HVRPrimeInfinite
open HVRPrimeZetaSplit HVRZetaBoundaryFactor

/-- The finite analytic order of the actual zeta function on the line. -/
def boundaryZetaOrder (t : ℝ) : ℕ :=
  analyticOrderNatAt riemannZeta (boundaryPoint t)

/-- Explicit residue-shaped limit for the negative logarithmic derivative
of actual zeta along the selected approach from the right. -/
def ZetaBoundaryResidueLimit (t : ℝ) : Prop :=
  Tendsto (fun n : ℕ => (boundaryEps n : ℂ) *
    (-deriv riemannZeta (zetaPoint (1 + boundaryEps n) t) /
      riemannZeta (zetaPoint (1 + boundaryEps n) t))) atTop
      (nhds (-(boundaryZetaOrder t : ℂ)))

theorem boundaryPoint_ne_one {t : ℝ} (ht : t ≠ 0) : boundaryPoint t ≠ 1 := by
  intro heq
  have him := congrArg Complex.im heq
  have ht0 : t = 0 := by simpa [boundaryPoint] using him
  exact ht ht0

/-- The two named zeta residue limits exclude a zero at the first ordinate.
The order at the doubled ordinate can be zero. -/
theorem nonvanishing_of_two_zeta_residues (t : ℝ) (ht : t ≠ 0)
    (hfirst : ZetaBoundaryResidueLimit t)
    (hsecond : ZetaBoundaryResidueLimit (2 * t)) :
    riemannZeta (boundaryPoint t) ≠ 0 := by
  intro hz
  have hsre : (boundaryPoint t).re = 1 := by simp [boundaryPoint]
  have horder : 1 ≤ boundaryZetaOrder t := by
    exact zeta_boundary_zero_order_pos (boundaryPoint t) hsre
      (boundaryPoint_ne_one ht) hz
  have hm : (1 : ℝ) ≤ (boundaryZetaOrder t : ℝ) := by exact_mod_cast horder
  have hq : (0 : ℝ) ≤ (boundaryZetaOrder (2 * t) : ℝ) := by positivity
  have hone : Tendsto (fun n : ℕ => boundaryEps n *
      cosMoment (1 + boundaryEps n) t 1) atTop
      (nhds (-(boundaryZetaOrder t : ℝ))) := by
    have h := cosMoment_limit_of_log_derivative
      (fun n => 1 + boundaryEps n) boundaryEps t 1
      (-(boundaryZetaOrder t : ℂ)) boundarySigma_gt_one
      (by simpa only [one_mul, ZetaBoundaryResidueLimit] using hfirst)
      (by simpa only [one_mul, boundaryApproach] using normalized_correction_tendsto_zero t)
    simpa only [Complex.neg_re, Complex.natCast_re] using h
  have htwo : Tendsto (fun n : ℕ => boundaryEps n *
      cosMoment (1 + boundaryEps n) t 2) atTop
      (nhds (-(boundaryZetaOrder (2 * t) : ℝ))) := by
    have h := cosMoment_limit_of_log_derivative
      (fun n => 1 + boundaryEps n) boundaryEps t 2
      (-(boundaryZetaOrder (2 * t) : ℂ)) boundarySigma_gt_one
      (by simpa only [ZetaBoundaryResidueLimit] using hsecond)
      (by simpa only [boundaryApproach] using normalized_correction_tendsto_zero (2 * t))
    simpa only [Complex.neg_re, Complex.natCast_re] using h
  exact residue_limits_contradict_prime_gram
    (fun n => 1 + boundaryEps n) boundaryEps t
    (boundaryZetaOrder t : ℝ) (boundaryZetaOrder (2 * t) : ℝ)
    boundarySigma_gt_one (fun n => le_of_lt (boundaryEps_pos n))
    normalized_primeMass_pole_limit hone htwo hm hq

/-- Conditional line-wide endpoint, with the missing analytic limit named. -/
theorem nonvanishing_of_all_zeta_residues
    (hres : ∀ t : ℝ, t ≠ 0 → ZetaBoundaryResidueLimit t) :
    ∀ t : ℝ, t ≠ 0 → riemannZeta (boundaryPoint t) ≠ 0 := by
  intro t ht
  have ht2 : 2 * t ≠ 0 := mul_ne_zero (by norm_num) ht
  exact nonvanishing_of_two_zeta_residues t ht (hres t ht) (hres (2 * t) ht2)

end HVRZetaGramResidueConditional
