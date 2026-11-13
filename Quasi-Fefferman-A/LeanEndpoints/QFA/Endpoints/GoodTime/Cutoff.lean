import QFA.Endpoints.GoodTime.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# QFA: the frozen 16*pi^2 cutoff and strict product selection

Project status: B_TIER. Lean status: A_TIER_CANDIDATE.
External compilation and theorem-level axiom audit are pending.

Proof index: QUASI_FEFFERMAN_A_ENTRYPOINT_COMPOSITION_B_TIER, version 1.2,
D05.01-D05.02. EP028 is used through the selective port in GoodTime.Basic.

QFA specification pin: 8a30134611027f99f4855c062f7903069cdca8d8.
QFB generic source pin: e6d7a34aba1549d098b0f8bd0caefd9dbdc85b0c.
Mathlib source pin: db584cd6d46c92f209a44c0f1c829460d327499d.
Selected external toolchain: leanprover/lean4:v4.33.0.

The QFB-specific 8*pi^2 cutoff theorem is not imported. The arithmetic below
uses the exact QFA product budget M^4/(4*nu) and threshold 4*pi^2*nu^4.
-/

set_option autoImplicit false
set_option Elab.async true

open MeasureTheory Set

namespace QFA.Endpoints.GoodTime

/-- D05.01: the frozen cutoff is nonnegative for positive viscosity.
No sign assumption on `M` is needed for its fourth power. -/
theorem qfa_cutoff_nonneg (M : ℝ) {ν : ℝ} (hν : 0 < ν) :
    0 ≤ M ^ 4 / (16 * Real.pi ^ 2 * ν ^ 5) := by
  positivity

/-- D05.01: the strict frozen cutoff gives precisely the strict average
needed for the subcritical product threshold. -/
theorem qfa_budget_lt_threshold
    {M ν δ : ℝ} (hν : 0 < ν)
    (hcut : M ^ 4 / (16 * Real.pi ^ 2 * ν ^ 5) < δ) :
    M ^ 4 / (4 * ν) < (4 * Real.pi ^ 2 * ν ^ 4) * δ := by
  have hden : 0 < 16 * Real.pi ^ 2 * ν ^ 5 := by positivity
  have hscaled : M ^ 4 < δ * (16 * Real.pi ^ 2 * ν ^ 5) :=
    (div_lt_iff₀ hden).mp hcut
  apply (div_lt_iff₀ (show 0 < 4 * ν by positivity)).2
  have heq : (4 * Real.pi ^ 2 * ν ^ 4) * δ * (4 * ν) =
      δ * (16 * Real.pi ^ 2 * ν ^ 5) := by ring
  rw [heq]
  exact hscaled

/-- D05.01-D05.02: the exact QFA budget produces a subcritical product time
while retaining the supplied almost-everywhere good-time predicate.

`E` and `D` are scalar inputs. This theorem does not assert that they arise
from a whole-space Leray-Hopf trajectory, or that `Good` entails restart. -/
theorem exists_subcritical_product_good_time
    {E D : ℝ → ℝ} {Good : ℝ → Prop} {M ν δ : ℝ}
    (hν : 0 < ν)
    (hcut : M ^ 4 / (16 * Real.pi ^ 2 * ν ^ 5) < δ)
    (hprod : Integrable (fun t => E t * D t)
      (volume.restrict (Ioo (0 : ℝ) δ)))
    (hgood : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) δ), Good t)
    (hbudget : (∫ t in Ioo (0 : ℝ) δ, E t * D t) ≤ M ^ 4 / (4 * ν)) :
    ∃ s, 0 < s ∧ s < δ ∧ Good s ∧ E s * D s < 4 * Real.pi ^ 2 * ν ^ 4 := by
  have hδ : 0 < δ := lt_of_le_of_lt (qfa_cutoff_nonneg M hν) hcut
  -- D05.01: retain the strict inequality obtained from the frozen cutoff.
  have hstrict : (∫ t in Ioo (0 : ℝ) δ, E t * D t) <
      (4 * Real.pi ^ 2 * ν ^ 4) * δ :=
    hbudget.trans_lt (qfa_budget_lt_threshold hν hcut)
  -- EP028 / D05.02, with f=E*D, c=4*pi^2*nu^4, T=delta, Good unchanged.
  exact exists_good_time_of_integral_lt
    (f := fun t => E t * D t) (Good := Good) (T := δ)
    (c := 4 * Real.pi ^ 2 * ν ^ 4)
    hδ (by positivity) hprod hgood hstrict

end QFA.Endpoints.GoodTime
