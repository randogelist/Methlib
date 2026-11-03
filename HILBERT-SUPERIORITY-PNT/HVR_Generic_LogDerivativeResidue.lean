import HVR_Prime_InfiniteGram

noncomputable section

/-!
A generic factored logarithmic-derivative limit. The sequence-level
factorisation and derivative identity needed to apply this to zeta are not
established here. In particular, no assertion of zeta boundary zero-freeness
is made.
-/
namespace HVRGenericLogDerivativeResidue

open Filter

/-- The logarithmic derivative of a factored germ, after multiplication by
its displacement. `u` represents the power factor and `v` the nonvanishing
analytic factor. -/
theorem factored_log_derivative_algebra
    (x u v dv : ℂ) (m : ℂ) (hx : x ≠ 0) (hu : u ≠ 0) (hv : v ≠ 0) :
    x * (((m : ℂ) * x⁻¹ * u * v + u * dv) / (u * v)) =
      (m : ℂ) + x * (dv / v) := by
  field_simp [hx, hu, hv]
  <;> ring

/-- If the displacement tends to zero and the nonvanishing factor and its
derivative have finite limits, the normalized logarithmic derivative of the
explicit factored expression tends to its prescribed coefficient. The coefficient
may be a nonnegative integer for a zero or -1 for a simple pole. The factorisation,
its derivative identity, and all nonvanishing hypotheses are explicit inputs;
this theorem does not establish them for zeta. -/
theorem factored_log_derivative_limit
    (x u v dv : ℕ → ℂ) (m : ℂ) (v0 dv0 : ℂ)
    (hx : ∀ n, x n ≠ 0) (hu : ∀ n, u n ≠ 0) (hv : ∀ n, v n ≠ 0)
    (hv0 : v0 ≠ 0)
    (hxlim : Tendsto x atTop (nhds 0))
    (hvlim : Tendsto v atTop (nhds v0))
    (hdvlim : Tendsto dv atTop (nhds dv0)) :
    Tendsto
      (fun n => x n * (((m : ℂ) * (x n)⁻¹ * u n * v n + u n * dv n) /
        (u n * v n))) atTop (nhds (m : ℂ)) := by
  have hlim : Tendsto (fun n => (m : ℂ) + x n * (dv n / v n))
      atTop (nhds (m : ℂ)) := by
    have hc : Tendsto (fun _ : ℕ => (m : ℂ)) atTop (nhds (m : ℂ)) :=
      tendsto_const_nhds
    have hprod := hxlim.mul (hdvlim.div hvlim hv0)
    simpa only [Pi.div_apply, zero_mul, add_zero] using hc.add hprod
  have heq :
      (fun n => x n * (((m : ℂ) * (x n)⁻¹ * u n * v n + u n * dv n) /
        (u n * v n))) =
      (fun n => (m : ℂ) + x n * (dv n / v n)) := by
    funext n
    exact factored_log_derivative_algebra (x n) (u n) (v n) (dv n) m
      (hx n) (hu n) (hv n)
  rw [heq]
  exact hlim

/-- An external application may supply a function value and derivative
sequence together with the displayed factorisation and derivative formula.
Those equalities are hypotheses, not claims about any particular function. -/
theorem factored_quotient_limit
    (x u v dv f df : ℕ → ℂ) (m : ℂ) (v0 dv0 : ℂ)
    (hx : ∀ n, x n ≠ 0) (hu : ∀ n, u n ≠ 0) (hv : ∀ n, v n ≠ 0)
    (hv0 : v0 ≠ 0)
    (hxlim : Tendsto x atTop (nhds 0))
    (hvlim : Tendsto v atTop (nhds v0))
    (hdvlim : Tendsto dv atTop (nhds dv0))
    (hf : ∀ n, f n = u n * v n)
    (hdf : ∀ n, df n = (m : ℂ) * (x n)⁻¹ * u n * v n + u n * dv n) :
    Tendsto (fun n => x n * (df n / f n)) atTop (nhds (m : ℂ)) := by
  have hlim := factored_log_derivative_limit x u v dv m v0 dv0
    hx hu hv hv0 hxlim hvlim hdvlim
  have heq : (fun n => x n * (df n / f n)) =
      (fun n => x n * (((m : ℂ) * (x n)⁻¹ * u n * v n + u n * dv n) /
        (u n * v n))) := by
    funext n
    rw [hf n, hdf n]
  rw [heq]
  exact hlim

end HVRGenericLogDerivativeResidue
