import HVR_Zeta_ZeroFreeBoundary
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Analysis.Complex.CauchyIntegral

noncomputable section

/-! Candidate local analytic pieces for the prime-only smoothing argument.
The prime-count transform and equality of these pieces on their overlaps are
not proved here.  External Lean build and axiom audit are required. -/
namespace HVRSmoothingAnalyticGerms

open HVRPowerCorrectionHolomorphic HVRCorrectionUniformBound
open HVRCorrectionBoundaryLimit HVRZetaBoundarySequence HVRZetaZeroFreeBoundary
open Filter
open scoped Topology

/-- Pole-subtracted candidate germ at z = 0. -/
def poleRegularPart (z : ℂ) : ℂ :=
  -(1 + deriv riemannZeta₁ (1 + z) / riemannZeta₁ (1 + z) +
      complexCorrection (1 + z)) / (1 + z)

/-- Correction-subtracted logarithmic derivative away from the pole. -/
def regularPartAt (s : ℂ) : ℂ :=
  (-deriv riemannZeta s / riemannZeta s - complexCorrection s) / s -
    (s - 1)⁻¹

theorem complexCorrection_differentiableAt_halfPlane (s : ℂ)
    (hs : (1 / 2 : ℝ) < s.re) : DifferentiableAt ℂ complexCorrection s := by
  let a : ℝ := ((1 / 2 : ℝ) + s.re) / 2
  have ha : (1 / 2 : ℝ) < a := by dsimp [a]; linarith
  have hm : s ∈ halfPlane a := by change a < s.re; dsimp [a]; linarith
  exact (complexCorrection_differentiableOn a ha s hm).differentiableAt
    ((halfPlane_isOpen a).mem_nhds hm)

/-- The explicitly regularized expression is holomorphic at the pole. -/
theorem poleRegularPart_differentiableAt_zero :
    DifferentiableAt ℂ poleRegularPart 0 := by
  have hshift : DifferentiableAt ℂ (fun z : ℂ => 1 + z) 0 := by fun_prop
  have hzeta : DifferentiableAt ℂ (fun z : ℂ => riemannZeta₁ (1 + z)) 0 := by
    exact (differentiable_riemannZeta₁ (1 + 0)).comp 0 hshift
  have hderiv : DifferentiableAt ℂ (fun z : ℂ => deriv riemannZeta₁ (1 + z)) 0 := by
    exact (differentiable_riemannZeta₁.deriv (1 + 0)).comp 0 hshift
  have hnz : riemannZeta₁ (1 + (0 : ℂ)) ≠ 0 := by simp
  have hratio := hderiv.div hzeta hnz
  have hc : DifferentiableAt ℂ (fun z : ℂ => complexCorrection (1 + z)) 0 := by
    apply (complexCorrection_differentiableAt_halfPlane (1 + 0) ?_).comp 0 hshift
    norm_num
  have hnum : DifferentiableAt ℂ (fun z : ℂ =>
      -(1 + deriv riemannZeta₁ (1 + z) / riemannZeta₁ (1 + z) +
        complexCorrection (1 + z))) 0 := by
    have hone : DifferentiableAt ℂ (fun _ : ℂ => (1 : ℂ)) 0 := by
      fun_prop
    exact ((hone.add hratio).add hc).neg
  have hden : (1 : ℂ) + 0 ≠ 0 := by norm_num
  exact hnum.div hshift hden

/-- At a regular, nonzero zeta point in Re(s)>1/2, the unshifted expression
is holomorphic. Zeta nonvanishing is an explicit pointwise hypothesis here. -/
theorem regularPartAt_differentiableAt (s : ℂ)
    (hs : s ≠ 1) (hs0 : s ≠ 0) (hz : riemannZeta s ≠ 0)
    (hre : (1 / 2 : ℝ) < s.re) : DifferentiableAt ℂ regularPartAt s := by
  have ha : AnalyticAt ℂ riemannZeta s := by
    apply analyticOn_riemannZeta
    simpa using hs
  have hderiv : DifferentiableAt ℂ (deriv riemannZeta) s := ha.deriv.differentiableAt
  have hquot : DifferentiableAt ℂ (fun z : ℂ => -deriv riemannZeta z / riemannZeta z) s :=
    hderiv.neg.div ha.differentiableAt hz
  have hc := complexCorrection_differentiableAt_halfPlane s hre
  have hid : DifferentiableAt ℂ (fun z : ℂ => z) s := differentiableAt_id
  have hwhole := (hquot.sub hc).div hid hs0
  have hinv : DifferentiableAt ℂ (fun z : ℂ => (z - 1)⁻¹) s := by
    have hsub : DifferentiableAt ℂ (fun z : ℂ => z - 1) s := by fun_prop
    exact hsub.inv (sub_ne_zero.mpr hs)
  exact hwhole.sub hinv

/-- The audited zero-free line supplies the nonvanishing hypotheses away from
the pole. -/
theorem regularPartAt_differentiableAt_boundary (t : ℝ) (ht : t ≠ 0) :
    DifferentiableAt ℂ regularPartAt (boundaryPoint t) := by
  apply regularPartAt_differentiableAt (boundaryPoint t)
  · exact boundaryPoint_ne_one t ht
  · intro hzero
    have hr := boundaryPoint_re t
    rw [hzero] at hr
    norm_num at hr
  · exact zeta_nonzero_on_one_line t ht
  · rw [boundaryPoint_re]
    norm_num


end HVRSmoothingAnalyticGerms
