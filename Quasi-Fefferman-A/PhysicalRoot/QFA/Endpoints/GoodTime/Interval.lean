import QFA.Endpoints.GoodTime.Cutoff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# QFA: interval-budget adapter for strict good-time extraction

Project status: B_TIER. Lean status: A_TIER_CANDIDATE.
External compilation and theorem-level axiom audit are pending.

Proof index: QUASI_FEFFERMAN_A_ENTRYPOINT_COMPOSITION_B_TIER, version 1.2:
  EP011  MeasureTheory.restrict_Ioo_eq_restrict_Ioc;
  EP012  intervalIntegrable_iff_integrableOn_Ioc_of_le;
  EP027  intervalIntegral.integral_of_le;
  EP028  generic strict-average extraction, selectively ported in Basic.

QFA specification pin: 8a30134611027f99f4855c062f7903069cdca8d8.
Mathlib source pin: db584cd6d46c92f209a44c0f1c829460d327499d.
Selected external toolchain: leanprover/lean4:v4.33.0.

This adapter changes only the time-integral representation. The actual
whole-space energy budget and the interpretation of `Good` remain inputs.
-/

set_option autoImplicit false
set_option Elab.async true

open MeasureTheory Set
open scoped Interval

namespace QFA.Endpoints.GoodTime

/-- The interval-integral form composes directly with the QFA scalar
energy-envelope budget. All integrability and a.e. good-time data remain
explicit; no arbitrary point is selected outside the good predicate. -/
theorem exists_subcritical_product_good_time_of_interval_budget
    {E D : ℝ → ℝ} {Good : ℝ → Prop} {M ν δ : ℝ}
    (hν : 0 < ν)
    (hcut : M ^ 4 / (16 * Real.pi ^ 2 * ν ^ 5) < δ)
    (hprod : IntervalIntegrable (fun t => E t * D t) volume 0 δ)
    (hgood : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) δ), Good t)
    (hbudget : (∫ t in (0 : ℝ)..δ, E t * D t) ≤ M ^ 4 / (4 * ν)) :
    ∃ s, 0 < s ∧ s < δ ∧ Good s ∧ E s * D s < 4 * Real.pi ^ 2 * ν ^ 4 := by
  have hδ : 0 < δ := lt_of_le_of_lt (qfa_cutoff_nonneg M hν) hcut
  -- EP011: the endpoint singleton has zero Lebesgue measure.
  have hmeasure : volume.restrict (Ioo (0 : ℝ) δ) =
      volume.restrict (Ioc (0 : ℝ) δ) :=
    restrict_Ioo_eq_restrict_Ioc
  -- EP012: positive orientation transports the actual interval integrability.
  have hprodIoc : Integrable (fun t => E t * D t)
      (volume.restrict (Ioc (0 : ℝ) δ)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hδ.le).mp hprod
  have hprodIoo : Integrable (fun t => E t * D t)
      (volume.restrict (Ioo (0 : ℝ) δ)) := by
    rw [hmeasure]
    exact hprodIoc
  -- EP027: interval integral = the actual half-open set integral.
  have hbudgetIoc : (∫ t in Ioc (0 : ℝ) δ, E t * D t) ≤
      M ^ 4 / (4 * ν) := by
    simpa only [intervalIntegral.integral_of_le hδ.le] using hbudget
  -- EP011 transports the same numerical budget to the open interval.
  have hbudgetIoo : (∫ t in Ioo (0 : ℝ) δ, E t * D t) ≤
      M ^ 4 / (4 * ν) := by
    change (∫ t, E t * D t ∂volume.restrict (Ioo (0 : ℝ) δ)) ≤ M ^ 4 / (4 * ν)
    rw [hmeasure]
    exact hbudgetIoc
  -- D05.01 and EP028, with the original a.e. predicate retained.
  exact exists_subcritical_product_good_time hν hcut hprodIoo hgood hbudgetIoo

end QFA.Endpoints.GoodTime
