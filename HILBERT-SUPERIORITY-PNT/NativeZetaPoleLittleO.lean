import NativeZetaPoleEquality
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Tactic

/-!
The logarithmic derivative near the pole, using the derivative of the
multiplicative regularization and the value of the additive regularization
at one. The latter is definitional. The differentiability of the additive
regularization enters upstream in `regularized_hasDerivAt`.
-/

noncomputable section

open Filter Asymptotics
open scoped Topology

namespace HVRNativeZetaPoleLittleO

open HVRNativeZetaPoleEquality

/-- The logarithmic derivative of the regularized factor tends to the
Euler--Mascheroni constant at the pole. -/
theorem regularized_log_derivative_tendsto :
    Tendsto (fun s : ℂ => deriv riemannZeta₁ s / riemannZeta₁ s)
      (𝓝[≠] (1 : ℂ)) (𝓝 (Real.eulerMascheroniConstant : ℂ)) := by
  have hnum : ContinuousAt (fun s : ℂ => deriv riemannZeta₁ s) (1 : ℂ) :=
    regularized_differentiable.deriv.continuous.continuousAt
  have hden : ContinuousAt riemannZeta₁ (1 : ℂ) :=
    regularized_differentiable.continuous.continuousAt
  have hne : riemannZeta₁ (1 : ℂ) ≠ 0 := regularized_value_one.trans_ne one_ne_zero
  have hc := hnum.div hden hne
  have ht : Tendsto (fun s : ℂ => deriv riemannZeta₁ s / riemannZeta₁ s)
      (𝓝[≠] (1 : ℂ))
      (𝓝 (deriv riemannZeta₁ (1 : ℂ) / riemannZeta₁ (1 : ℂ))) :=
    hc.tendsto.mono_left nhdsWithin_le_nhds
  simpa only [regularized_derivative_one, regularized_value_one, div_one] using ht

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
  filter_upwards [HVRNativeZetaPoleEquality.log_derivative_eventually_eq] with s hs
  rw [hs]
  ring

end HVRNativeZetaPoleLittleO

