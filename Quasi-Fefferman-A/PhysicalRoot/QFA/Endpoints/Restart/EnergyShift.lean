import QFA.Endpoints.Restart.TimeTranslate

/-!
# QFA: scalar energy consequences at a supplied restart time

Project status: B_TIER. This file is an A_TIER_CANDIDATE only.
External compilation and theorem-level axiom audit are pending.
No local Lean or Lake execution is authorized by this file.

Proof index: QUASI_FEFFERMAN_A_ENTRYPOINT_COMPOSITION_B_TIER, version 1.2,
D05.03--D05.04 / EP034--EP035.

Selective source pattern:
  repository: randogelist/Methlib
  commit: e6d7a34aba1549d098b0f8bd0caefd9dbdc85b0c
  file: Quasi-Fefferman-B/QuasiFeffermanB/LHRestart.lean
  source blob: 99c8781a467659b4a44da1a22f284e15f375e523
  declarations/fragments: lh_energy_le_from_start;
    energy_initial and energy_intervals in LH_RESTART_FROM_ENERGY_START

The scalar profiles E and D replace the source's periodic spatial objects.
Every energy inequality is an explicit premise. No weak momentum equation,
trajectory existence, PDE restart theorem, or regularity conclusion occurs.

Mathlib pin: db584cd6d46c92f209a44c0f1c829460d327499d.
External toolchain: leanprover/lean4:v4.33.0.

Trajectory applications restrict identity and singleton statements to
nonnegative time. Auxiliary real-time extensions are not identified at
negative times. The inequalities below preserve their stated time domains.
-/

set_option autoImplicit false
set_option Elab.async true

open Set Filter MeasureTheory
open scoped ENNReal Topology Interval

namespace QFA.Endpoints.Restart

noncomputable section

/-- D05.03: nonnegative dissipation makes the supplied energy-start
inequality imply an upper energy bound for every later time. Positivity of
D is required only on the nonnegative physical time domain. -/
theorem energy_le_of_energy_start
    {E D : ℝ → ℝ} {ν s t : ℝ}
    (hν : 0 ≤ ν) (hs : 0 ≤ s)
    (hD : ∀ r : ℝ, 0 ≤ r → 0 ≤ D r)
    (hE : ∀ r : ℝ, s ≤ r →
      E r + 2 * ν * (∫ q in s..r, D q) ≤ E s)
    (hst : s ≤ t) :
    E t ≤ E s := by
  -- Generic adaptation of lh_energy_le_from_start: interval positivity
  -- uses only r in [s,t], hence only nonnegative physical times.
  have hDint : 0 ≤ ∫ r in s..t, D r :=
    intervalIntegral.integral_nonneg hst (fun r hr => hD r (hs.trans hr.1))
  have hprod : 0 ≤ 2 * ν * (∫ r in s..t, D r) :=
    mul_nonneg (mul_nonneg (by norm_num) hν) hDint
  linarith only [hE t hst, hprod]

/-- D05.04 / EP035: the supplied all-time energy inequality at s becomes
the zero-start energy inequality for the translated profiles. -/
theorem timeTranslate_energy_from_start
    {E D : ℝ → ℝ} {ν s : ℝ}
    (hE : ∀ r : ℝ, s ≤ r →
      E r + 2 * ν * (∫ q in s..r, D q) ≤ E s) :
    ∀ t : ℝ, 0 ≤ t →
      timeTranslate s E t +
        2 * ν * (∫ q in (0 : ℝ)..t, timeTranslate s D q) ≤ E s := by
  intro t ht
  change E (t + s) + 2 * ν * (∫ q in (0 : ℝ)..t, D (q + s)) ≤ E s
  -- EP035 transports the entire dissipation interval, including its start.
  rw [intervalIntegral.integral_comp_add_right D s, zero_add]
  exact hE (t + s) (by linarith)

/-- D05.04 / EP034--EP035: almost-everywhere valid energy starts retain
the inequality at every later upper endpoint in the translated horizon. -/
theorem timeTranslate_energy_intervals
    {E D : ℝ → ℝ} {ν s T : ℝ} (hs : 0 ≤ s)
    (hE : ∀ᵐ r ∂volume.restrict (Ioc (0 : ℝ) (T + s)),
      ∀ t ∈ Icc r (T + s),
        E t + 2 * ν * (∫ q in r..t, D q) ≤ E r) :
    ∀ᵐ r ∂volume.restrict (Ioc (0 : ℝ) T),
      ∀ t ∈ Icc r T,
        timeTranslate s E t +
          2 * ν * (∫ q in r..t, timeTranslate s D q) ≤ timeTranslate s E r := by
  -- EP034 transports the supplied valid-start predicate.
  have hshift := timeTranslate_ae_Ioc hs hE
  filter_upwards [hshift] with r hr
  intro t ht
  change E (t + s) + 2 * ν * (∫ q in r..t, D (q + s)) ≤ E (r + s)
  -- EP035 transports the integral; both endpoint inequalities are retained.
  rw [intervalIntegral.integral_comp_add_right D s]
  exact hr (t + s) ⟨by linarith [ht.1], by linarith [ht.2]⟩

end

end QFA.Endpoints.Restart
