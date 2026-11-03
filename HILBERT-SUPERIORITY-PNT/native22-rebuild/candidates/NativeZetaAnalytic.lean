import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Tactic

/-!
Candidate analytic continuation interface via the regularized zeta function.

This source builds the exact analytic-away-from-one statement by differentiating
the regularized-factor representation. It uses Mathlib's entire regularized
zeta function and the factorization away from one. In the pinned Mathlib
source, regularized-zeta differentiability is itself derived using the
existing differentiability of zeta away from one. Thus this is a direct-call
replacement candidate, not an independent reconstruction of that analytic
foundation. A matching compiler run and named axiom audit remain required.
-/

noncomputable section

open Filter
open scoped Topology

namespace HVRNativeZetaAnalytic

/-- Away from its pole, actual zeta is differentiable by the regularized
factor representation. -/
theorem differentiableOn_zeta_via_regularized :
    DifferentiableOn ℂ riemannZeta ({(1 : ℂ)}ᶜ) := by
  intro s hs
  have hne : s ≠ (1 : ℂ) := by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hs
  have hsub : DifferentiableAt ℂ (fun z : ℂ => z - 1) s := by
    fun_prop
  have hreg : DifferentiableAt ℂ
      (fun z : ℂ => (z - 1)⁻¹ * riemannZeta₁ z) s :=
    (hsub.inv (sub_ne_zero.mpr hne)).mul (differentiable_riemannZeta₁ s)
  have heq : riemannZeta =ᶠ[𝓝 s]
      (fun z : ℂ => (z - 1)⁻¹ * riemannZeta₁ z) := by
    filter_upwards [continuousAt_id.eventually_ne hne] with z hz
    exact riemannZeta_eq_inv_sub_mul hz
  exact (hreg.congr_of_eventuallyEq heq).differentiableWithinAt

/-- Actual zeta is analytic on a neighborhood of every complex point except
one. This matches the domain and conclusion of the corresponding library
analyticity statement. -/
theorem analyticOn_zeta_via_regularized :
    AnalyticOnNhd ℂ riemannZeta ({(1 : ℂ)}ᶜ) :=
  differentiableOn_zeta_via_regularized.analyticOnNhd isOpen_compl_singleton

end HVRNativeZetaAnalytic
