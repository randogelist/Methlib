import HVR_Zeta_CorrectionIdentity
import IntegratedZetaNonzero
import NativeZetaPoleEquality
import Mathlib.Analysis.Analytic.Order

noncomputable section
open Filter

/-!
Candidate finite-order local factorization of actual zeta at points of the
line Re z=1 away from its pole. The proof uses zeta nonvanishing only on
the open half-plane Re z>1. It does not establish nonvanishing on the line.
An external Lean build, axiom audit and theorem-dependency inspection remain
required. No Lean run was performed locally.
-/
namespace HVRZetaBoundaryFactor

/-- Zeta cannot be identically zero in any neighborhood of a point on the
line Re z=1, since each such neighborhood meets Re z>1. -/
theorem zeta_boundary_finite_order (s : ℂ) (hsre : s.re = 1) :
    analyticOrderAt riemannZeta s ≠ ⊤ := by
  intro htop
  have hz : ∀ᶠ z in nhds s, riemannZeta z = 0 :=
    analyticOrderAt_eq_top.mp htop
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hz
  have hhalf : 0 < ε / 2 := by linarith
  have hright : 1 < (s + ((ε / 2 : ℝ) : ℂ)).re := by
    simp only [Complex.add_re, Complex.ofReal_re, hsre]
    linarith
  have hdist : dist (s + ((ε / 2 : ℝ) : ℂ)) s < ε := by
    rw [dist_eq_norm]
    have heq : s + ((ε / 2 : ℝ) : ℂ) - s = ((ε / 2 : ℝ) : ℂ) := by ring
    rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hhalf]
    linarith
  exact (HVRIntegratedZetaNonzero.zeta_ne_zero_of_one_lt_re hright) (hball hdist)

/-- At every such regular point, zeta has its actual finite-order analytic
factorization. Order zero covers a nonzero value. -/
theorem zeta_boundary_local_factor (s : ℂ) (hsre : s.re = 1) (hsne : s ≠ 1) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g s ∧ g s ≠ 0 ∧
      riemannZeta =ᶠ[nhds s] fun z =>
        (z - s) ^ (analyticOrderNatAt riemannZeta s) * g z := by
  have ha : AnalyticAt ℂ riemannZeta s := HVRNativeZetaPoleEquality.zeta_analyticAt hsne
  obtain ⟨g, hg, hgn, hfac⟩ :=
    ha.analyticOrderAt_ne_top.mp (zeta_boundary_finite_order s hsre)
  refine ⟨g, hg, hgn, ?_⟩
  filter_upwards [hfac] with z hz
  simpa only [smul_eq_mul] using hz

/-- A hypothetical boundary zero has positive finite natural order. -/
theorem zeta_boundary_zero_order_pos (s : ℂ) (hsre : s.re = 1)
    (hsne : s ≠ 1) (hz : riemannZeta s = 0) :
    0 < analyticOrderNatAt riemannZeta s := by
  obtain ⟨g, _, hgn, hfac⟩ := zeta_boundary_local_factor s hsre hsne
  have hval := hfac.self_of_nhds
  by_contra hnot
  have hzero : analyticOrderNatAt riemannZeta s = 0 := Nat.eq_zero_of_not_pos hnot
  simp only [hzero, pow_zero, one_mul] at hval
  exact hgn (hval.symm.trans hz)

end HVRZetaBoundaryFactor
