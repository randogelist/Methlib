import HVR_Correction_UniformBound
import HVR_Prime_ZetaSplit
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section

/-!
The actual holomorphic correction is continuous at every point with real
part greater than one half. Along the concrete sequence approaching 1+it
from the right, the correction has a finite limit and the normalized
correction tends to zero. This does not assert any zeta residue limit,
boundary nonvanishing, or the prime number theorem. External compilation
and theorem-level axiom audits are required.
-/
namespace HVRCorrectionBoundaryLimit

open Filter HVRPowerCorrectionHolomorphic HVRCorrectionUniformBound
open HVRPrimeZetaSplit

def boundaryEps (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

def boundaryPoint (t : ℝ) : ℂ := 1 + (t : ℂ) * Complex.I

def boundaryApproach (t : ℝ) (n : ℕ) : ℂ :=
  zetaPoint (1 + boundaryEps n) t

theorem boundaryEps_pos (n : ℕ) : 0 < boundaryEps n := by
  unfold boundaryEps
  positivity

theorem boundarySigma_gt_one (n : ℕ) : 1 < 1 + boundaryEps n := by
  have h := boundaryEps_pos n
  linarith

theorem boundaryEps_tendsto : Tendsto boundaryEps atTop (nhds 0) := by
  exact tendsto_one_div_add_atTop_nhds_zero_nat

theorem boundaryEps_complex_tendsto :
    Tendsto (fun n : ℕ => (boundaryEps n : ℂ)) atTop (nhds 0) := by
  have h := (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp boundaryEps_tendsto
  simpa only [Complex.ofReal_zero, Function.comp_def] using h

theorem boundaryApproach_eq (t : ℝ) (n : ℕ) :
    boundaryApproach t n = boundaryPoint t + (boundaryEps n : ℂ) := by
  simp only [boundaryApproach, zetaPoint, boundaryPoint, Complex.ofReal_add,
    Complex.ofReal_one]
  ring

theorem boundaryApproach_tendsto (t : ℝ) :
    Tendsto (boundaryApproach t) atTop (nhds (boundaryPoint t)) := by
  have h : Tendsto (fun n : ℕ => boundaryPoint t + (boundaryEps n : ℂ))
      atTop (nhds (boundaryPoint t + 0)) :=
    tendsto_const_nhds.add boundaryEps_complex_tendsto
  simpa only [add_zero, ← boundaryApproach_eq] using h

theorem complexCorrection_continuousAt (z : ℂ) (hz : (1 / 2 : ℝ) < z.re) :
    ContinuousAt complexCorrection z := by
  let a : ℝ := ((1 / 2 : ℝ) + z.re) / 2
  have ha : (1 / 2 : ℝ) < a := by dsimp [a]; linarith
  have hzmem : z ∈ halfPlane a := by
    change a < z.re
    dsimp [a]
    linarith
  have hd := complexCorrection_differentiableOn a ha z hzmem
  exact (hd.differentiableAt ((halfPlane_isOpen a).mem_nhds hzmem)).continuousAt

theorem complexCorrection_tendsto_boundary (t : ℝ) :
    Tendsto (fun n : ℕ => complexCorrection (boundaryApproach t n)) atTop
      (nhds (complexCorrection (boundaryPoint t))) := by
  have hre : (boundaryPoint t).re = 1 := by simp [boundaryPoint]
  have hz : (1 / 2 : ℝ) < (boundaryPoint t).re := by rw [hre]; norm_num
  exact (complexCorrection_continuousAt (boundaryPoint t) hz).tendsto.comp
    (boundaryApproach_tendsto t)

theorem normalized_correction_tendsto_zero (t : ℝ) :
    Tendsto (fun n : ℕ => (boundaryEps n : ℂ) *
      complexCorrection (boundaryApproach t n)) atTop (nhds 0) := by
  have h := boundaryEps_complex_tendsto.mul (complexCorrection_tendsto_boundary t)
  simpa only [zero_mul] using h

/-- The real-part form used by the nonnegative prime Gram inequality. -/
theorem normalized_correction_re_tendsto_zero (t : ℝ) :
    Tendsto (fun n : ℕ => boundaryEps n *
      (complexCorrection (boundaryApproach t n)).re) atTop (nhds 0) := by
  have h := (Complex.continuous_re.tendsto (0 : ℂ)).comp
    (normalized_correction_tendsto_zero t)
  simpa only [Function.comp_def, Complex.zero_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using h

end HVRCorrectionBoundaryLimit
