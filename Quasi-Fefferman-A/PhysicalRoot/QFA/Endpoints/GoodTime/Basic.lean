import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# QFA: strict-average extraction with an almost-everywhere good predicate

Project status: B_TIER. This Lean file is an A_TIER_CANDIDATE only.
External compilation and theorem-level axiom audit are pending.
No local Lean execution is authorized by this file.

Proof index: QUASI_FEFFERMAN_A_ENTRYPOINT_COMPOSITION_B_TIER, version 1.2,
D05.02 / EP028.

Selective source port:
  repository: randogelist/Methlib
  commit: e6d7a34aba1549d098b0f8bd0caefd9dbdc85b0c
  file: Quasi-Fefferman-B/QuasiFeffermanB/GoodTime.lean
  declaration: QuasiFeffermanB.exists_good_time_of_integral_lt
  source blob: 628486116b7120e5e66cfcfcae08693b7516933b

Changes from the generic source: namespace and explicit restricted Lebesgue
measure in place of `criticalTimeMeasure`. No periodic PDE module is imported.

Mathlib source pin: db584cd6d46c92f209a44c0f1c829460d327499d.
Selected external toolchain: leanprover/lean4:v4.33.0.
-/

set_option autoImplicit false
set_option Elab.async true

open MeasureTheory Set

namespace QFA.Endpoints.GoodTime

/-- EP028 / D05.02: a strict integral bound produces a point in `(0,T)`
retaining any supplied almost-everywhere predicate. Neither continuity of
`f` nor measurability of the set defined by `Good` is imposed. -/
theorem exists_good_time_of_integral_lt
    {f : ℝ → ℝ} {Good : ℝ → Prop} {T c : ℝ}
    (hT : 0 < T) (hc : 0 ≤ c)
    (hf : Integrable f (volume.restrict (Ioo (0 : ℝ) T)))
    (hgood : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) T), Good t)
    (hbudget : (∫ t in Ioo (0 : ℝ) T, f t) < c * T) :
    ∃ t, 0 < t ∧ t < T ∧ Good t ∧ f t < c := by
  -- EP028 source body: absence of a good witness forces an a.e. lower bound.
  by_contra hnone
  have hlower : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) T), c ≤ f t := by
    have htime : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) T), t ∈ Ioo 0 T :=
      ae_restrict_mem measurableSet_Ioo
    filter_upwards [htime, hgood] with t ht hg
    by_contra hnot
    exact hnone ⟨t, ht.1, ht.2, hg, lt_of_not_ge hnot⟩
  -- EP028 source body: integral monotonicity needs the retained integrability.
  -- Mathlib/MeasureTheory/Integral/Bochner/Basic.lean: integral_mono_of_nonneg.
  have hcomparison :
      (∫ _ in Ioo (0 : ℝ) T, c) ≤
        ∫ t in Ioo (0 : ℝ) T, f t :=
    integral_mono_of_nonneg (ae_of_all _ (fun _ => hc)) hf hlower
  -- EP028 source body: setIntegral_const and Real.volume_Ioo evaluate the
  -- Lebesgue integral of the threshold on the actual interval.
  have hconstant : (∫ _ in Ioo (0 : ℝ) T, c) = c * T := by
    rw [setIntegral_const]
    simp [Measure.real, Real.volume_Ioo, hT.le, mul_comm]
  rw [hconstant] at hcomparison
  exact (not_lt_of_ge hcomparison) hbudget

end QFA.Endpoints.GoodTime
