import QFA.Endpoints.Energy.ProductBudget
import QFA.Endpoints.GoodTime.Cutoff

/-!
# QFA scalar endpoint composition: energy envelope to a strict good time

Derivation locations: D04.01-D04.06 -> D05.01-D05.02.
Existing source indices: EP011-EP028, at their constituent proof steps.

Status: A_TIER_CANDIDATE. Matching external compilation and exact theorem-level
axiom audit are pending. Mathematical derivation: B_TIER.

This theorem has scalar functions E,D and an arbitrary full-measure predicate
Good. Its conclusion is a good scalar time. Actual whole-space LH membership,
H1 representatives, and the translated physical weak equation must supply
the corresponding profile and predicate before a physical restart follows.
The frozen root theorem QUASI_FEFFERMAN_A is not declared in this module.
-/

set_option autoImplicit false
set_option Elab.async true

open MeasureTheory Set
open scoped Interval

namespace QFA.Endpoints.Composition

/-- Deterministic composition of the full AC budget with the exact QFA
16*pi^2 cutoff. The product-budget inequality is derived, not assumed. -/
theorem exists_subcritical_good_time_of_envelope
    {E D : ℝ → ℝ} {Good : ℝ → Prop} {M ν δ : ℝ}
    (hν : 0 < ν)
    (hcut : M ^ 4 / (16 * Real.pi ^ 2 * ν ^ 5) < δ)
    (hD : IntervalIntegrable D volume (0 : ℝ) δ)
    (hEm : AEStronglyMeasurable E (volume.restrict (Ioo (0 : ℝ) δ)))
    (hDnn : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) δ), 0 ≤ D t)
    (hEnn : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) δ), 0 ≤ E t)
    (hEF : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) δ),
      E t ≤ QFA.Energy.envelope M ν D t)
    (hgood : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) δ), Good t) :
    ∃ s, 0 < s ∧ s < δ ∧ Good s ∧ E s * D s < 4 * Real.pi ^ 2 * ν ^ 4 := by
  -- D05.01: positivity of the observation interval follows from the cutoff.
  have hδ : 0 < δ :=
    lt_of_le_of_lt (QFA.Endpoints.GoodTime.qfa_cutoff_nonneg M hν) hcut
  -- D04.02-D04.06 / EP013-EP027: actual product integrability and budget.
  obtain ⟨hprod, hbudget⟩ :=
    QFA.Energy.product_budget_Ioo hδ.le hν hD hEm hDnn hEnn hEF
  -- D05.01-D05.02 / EP028: keep Good in the witness selection.
  exact QFA.Endpoints.GoodTime.exists_subcritical_product_good_time
    hν hcut hprod hgood hbudget

end QFA.Endpoints.Composition
