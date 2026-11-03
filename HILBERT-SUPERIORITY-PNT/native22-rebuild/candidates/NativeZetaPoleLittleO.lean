import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Tactic

/-!
Candidate local zeta logarithmic-derivative asymptotic from a regularized
analytic factor. The proof uses Mathlib's eventual logarithmic-derivative
factorization, the entire regularized function, and its value and derivative
at one; it does not call the library little-o endpoint being reconstructed.
These regularized-factor ingredients remain Mathlib dependencies. A complete
declaration-dependency review and external compiler/audit are still required.
-/

noncomputable section

open Filter Asymptotics
open scoped Topology

namespace HVRNativeZetaPoleLittleO

/-- The logarithmic derivative of the regularized factor tends to the
Euler--Mascheroni constant at the pole. -/
theorem regularized_log_derivative_tendsto :
    Tendsto (fun s : ℂ => deriv riemannZeta₁ s / riemannZeta₁ s)
      (𝓝[≠] (1 : ℂ)) (𝓝 (Real.eulerMascheroniConstant : ℂ)) := by
  have hnum : ContinuousAt (fun s : ℂ => deriv riemannZeta₁ s) (1 : ℂ) :=
    differentiable_riemannZeta₁.deriv.continuous.continuousAt
  have hden : ContinuousAt riemannZeta₁ (1 : ℂ) :=
    differentiable_riemannZeta₁.continuous.continuousAt
  have hne : riemannZeta₁ (1 : ℂ) ≠ 0 := by simp
  have hc := hnum.div hden hne
  have ht : Tendsto (fun s : ℂ => deriv riemannZeta₁ s / riemannZeta₁ s)
      (𝓝[≠] (1 : ℂ))
      (𝓝 (deriv riemannZeta₁ (1 : ℂ) / riemannZeta₁ (1 : ℂ))) :=
    hc.tendsto.mono_left nhdsWithin_le_nhds
  simpa only [deriv_riemannZeta₁_one, riemannZeta₁_one, div_one] using ht

/-- At the actual zeta pole, the regularized logarithmic derivative minus
Euler's constant is little-o of the constant one. -/
theorem zeta_log_derivative_regularized_isLittleO :
    (fun s : ℂ => deriv riemannZeta s / riemannZeta s + (s - 1)⁻¹ -
      (Real.eulerMascheroniConstant : ℂ)) =o[𝓝[≠] (1 : ℂ)] (fun _ : ℂ => (1 : ℂ)) := by
  apply (isLittleO_one_iff ℂ).mpr
  have hz : Tendsto
      (fun s : ℂ => deriv riemannZeta₁ s / riemannZeta₁ s -
        (Real.eulerMascheroniConstant : ℂ))
      (𝓝[≠] (1 : ℂ)) (𝓝 (0 : ℂ)) := by
    simpa only [sub_self] using
      regularized_log_derivative_tendsto.sub_const (Real.eulerMascheroniConstant : ℂ)
  apply hz.congr'
  filter_upwards [log_deriv_riemannZeta_eq_neg_inv_sub_add] with s hs
  rw [hs]
  ring

end HVRNativeZetaPoleLittleO
