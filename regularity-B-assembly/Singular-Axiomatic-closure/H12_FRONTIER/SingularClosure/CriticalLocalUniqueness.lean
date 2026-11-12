import SingularClosure.CriticalUniqueness

/-! The admissible-time comparison only needs local integrability of the
coefficient times the relative energy.  The coefficient itself has a genuine
integrable bound up to the initial time. -/

set_option autoImplicit false
set_option Elab.async true

open Set Filter MeasureTheory
open scoped Topology Interval

namespace SingularClosure

noncomputable section

theorem CRITICAL_RELATIVE_ENERGY_ZERO_OF_LOCAL_ADMISSIBLE_TRACE
    {e a : ℝ → ℝ} {T M : ℝ} {ε : ℕ → ℝ}
    (hT : 0 < T)
    (he_nonneg : ∀ t ∈ Ioc 0 T, 0 ≤ e t)
    (ha : ContinuousOn a (Ioc 0 T))
    (ha_nonneg : ∀ t ∈ Ioc 0 T, 0 ≤ a t)
    (ha_integrable : IntervalIntegrable a volume 0 T)
    (hprod : ∀ n, IntervalIntegrable (fun r => a r * e r) volume (ε n) T)
    (hbudget : (∫ r in (0 : ℝ)..T, a r) ≤ M)
    (hε : ∀ n, ε n ∈ Ioc 0 T)
    (hε_zero : Tendsto ε atTop (𝓝 0))
    (htrace : Tendsto (fun n => e (ε n)) atTop (𝓝 0))
    (hrelative : ∀ n t, t ∈ Icc (ε n) T →
      e t ≤ e (ε n) + ∫ r in ε n..t, a r * e r) :
    ∀ t ∈ Ioc 0 T, e t = 0 := by
  intro t ht
  have hevent : ∀ᶠ n : ℕ in atTop, ε n < t :=
    hε_zero.eventually (Iio_mem_nhds ht.1)
  have hbound : ∀ᶠ n : ℕ in atTop, e t ≤ e (ε n) * Real.exp M := by
    filter_upwards [hevent] with n hnt
    have hsubset : Icc (ε n) T ⊆ Ioc 0 T := by
      intro r hr
      exact ⟨lt_of_lt_of_le (hε n).1 hr.1, hr.2⟩
    have hlocal := CRITICAL_RELATIVE_ENERGY_GRONWALL (hε n).2
      (ha.mono hsubset) (fun r hr => ha_nonneg r (hsubset hr)) (hprod n) (hrelative n)
    have hA : (∫ r in ε n..t, a r) ≤ M := by
      apply le_trans _ hbudget
      apply intervalIntegral.integral_mono_interval (hε n).1.le hnt.le ht.2
        _ ha_integrable
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      exact ha_nonneg r hr
    exact (hlocal t ⟨hnt.le, ht.2⟩).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hA) (he_nonneg (ε n) (hε n)))
  have hlim : Tendsto (fun n => e (ε n) * Real.exp M) atTop (𝓝 0) := by
    simpa only [zero_mul] using htrace.mul_const (Real.exp M)
  exact le_antisymm (ge_of_tendsto hlim hbound) (he_nonneg t ht)

end

end SingularClosure
