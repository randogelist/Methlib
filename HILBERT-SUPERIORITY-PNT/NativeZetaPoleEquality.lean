import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Tactic

/-!
Local calculus for the multiplicative regularization of zeta, starting from
the differentiability of the additive regularization. All identities use the
actual Mathlib zeta functions, including their values at the pole.
-/

noncomputable section

open Filter
open scoped Topology

namespace HVRNativeZetaPoleEquality

/-- Product rule for the entire factor `1 + (s - 1) * riemannZeta₀ s`. -/
theorem regularized_hasDerivAt (s : ℂ) :
    HasDerivAt riemannZeta₁ (riemannZeta₀ s + (s - 1) * deriv riemannZeta₀ s) s := by
  have hlin : HasDerivAt (fun z : ℂ => z - 1) 1 s := (hasDerivAt_id s).sub_const 1
  have hmul := hlin.mul (differentiable_riemannZeta₀ s).hasDerivAt
  simpa only [riemannZeta₁, Pi.mul_apply, one_mul] using hmul.const_add (1 : ℂ)

theorem regularized_differentiable : Differentiable ℂ riemannZeta₁ :=
  fun s => (regularized_hasDerivAt s).differentiableAt

theorem regularized_value_one : riemannZeta₁ 1 = 1 := by
  simp only [riemannZeta₁, sub_self, zero_mul, add_zero]

/-- Off the pole, undo both regularizations using their definitions. -/
theorem regularized_div_sub_one {s : ℂ} (hs : s ≠ 1) :
    riemannZeta₁ s / (s - 1) = riemannZeta s := by
  simp only [riemannZeta₁, riemannZeta₀, if_neg hs]
  field_simp [sub_ne_zero.mpr hs] <;> ring

/-- Away from one the quotient of the entire regularized factor by the
linear factor agrees locally with the actual zeta function. -/
theorem quotient_eventually_eq_zeta {s : ℂ} (hs : s ≠ 1) :
    (fun z : ℂ => riemannZeta₁ z / (z - 1)) =ᶠ[𝓝 s] riemannZeta := by
  filter_upwards [compl_singleton_mem_nhds hs] with z hz
  exact regularized_div_sub_one (Set.mem_compl_singleton_iff.mp hz)

/-- The actual zeta function is analytic at each point other than one. -/
theorem zeta_analyticAt {s : ℂ} (hs : s ≠ 1) : AnalyticAt ℂ riemannZeta s := by
  have hlin : AnalyticAt ℂ (fun z : ℂ => z - 1) s := analyticAt_id.sub analyticAt_const
  have hquot : AnalyticAt ℂ (fun z : ℂ => riemannZeta₁ z / (z - 1)) s :=
    (regularized_differentiable.analyticAt s).div hlin (sub_ne_zero.mpr hs)
  exact hquot.congr (quotient_eventually_eq_zeta hs)

/-- Pointwise logarithmic-derivative identity from the derivative of a quotient. -/
theorem log_derivative_eq {s : ℂ} (hs : s ≠ 1)
    (hreg : riemannZeta₁ s ≠ 0) :
    deriv riemannZeta s / riemannZeta s =
      - (s - 1)⁻¹ + deriv riemannZeta₁ s / riemannZeta₁ s := by
  have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  have hf := quotient_eventually_eq_zeta hs
  have hlin : HasDerivAt (fun z : ℂ => z - 1) 1 s := (hasDerivAt_id s).sub_const 1
  have hd := ((regularized_differentiable s).hasDerivAt.fun_div hlin hsub).deriv
  rw [← hf.deriv_eq, hd, ← regularized_div_sub_one hs]
  field_simp [hsub, hreg] <;> ring

/-- Nonvanishing of the regularized factor near its unit value. -/
theorem regularized_eventually_ne : ∀ᶠ s : ℂ in 𝓝 1, riemannZeta₁ s ≠ 0 :=
  (regularized_differentiable 1).continuousAt.tendsto.eventually_ne
    (regularized_value_one.trans_ne one_ne_zero)

/-- The pointwise identity holds on a punctured neighborhood of the pole. -/
theorem log_derivative_eventually_eq :
    ∀ᶠ s : ℂ in 𝓝[≠] (1 : ℂ),
      deriv riemannZeta s / riemannZeta s =
        - (s - 1)⁻¹ + deriv riemannZeta₁ s / riemannZeta₁ s := by
  filter_upwards [self_mem_nhdsWithin, regularized_eventually_ne.filter_mono nhdsWithin_le_nhds] with s hs hreg
  exact log_derivative_eq (Set.mem_compl_singleton_iff.mp hs) hreg

end HVRNativeZetaPoleEquality
