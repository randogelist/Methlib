import QFA.Endpoints.Restart.EnergyShift
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# QFA: strong Hilbert traces from weak pairing and an energy-start bound

Project status: B_TIER. This file is an A_TIER_CANDIDATE only.
External compilation and theorem-level axiom audit are pending.
No local Lean or Lake execution is authorized by this file.

Proof index: QUASI_FEFFERMAN_A_ENTRYPOINT_COMPOSITION_B_TIER, version 1.2,
D05.03 / EP029--EP031.

Selective source port:
  repository: randogelist/Methlib
  commit: e6d7a34aba1549d098b0f8bd0caefd9dbdc85b0c
  file: Quasi-Fefferman-B/QuasiFeffermanB/LHRestart.lean
  source blob: 99c8781a467659b4a44da1a22f284e15f375e523
  declaration: strong_tendsto_of_inner_and_norm_bound
  adapted source pattern: lh_strong_right_trace_of_energy_start

The carrier is an arbitrary real inner-product space. Completeness is not
required. The stronger physical interpretation as spatial L2 is supplied
by the application, together with the exact norm and pairing identities.
No periodic representation or PDE module is imported.

Mathlib pin: db584cd6d46c92f209a44c0f1c829460d327499d.
External toolchain: leanprover/lean4:v4.33.0.

The trajectory premises concern Ici 0 and a selected s >= 0. All right
limits therefore use physical nonnegative times. A later singleton claim
must remain restricted to that domain; equality of auxiliary negative-time
extensions is not a conclusion of these lemmas.
-/

set_option autoImplicit false
set_option Elab.async true

open Set Filter MeasureTheory
open scoped ENNReal Topology Interval

namespace QFA.Endpoints.Restart

noncomputable section

/-- EP029 / D05.03: convergence of the pairing with a and the eventual
upper bound by its squared norm imply strong convergence to a. -/
theorem strong_tendsto_of_inner_and_norm_bound
    {ι : Type*} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {l : Filter ι} {f : ι → E} {a : E}
    (hinner : Tendsto (fun i => inner ℝ (f i) a) l (𝓝 (‖a‖ ^ 2)))
    (hbound : ∀ᶠ i in l, ‖f i‖ ^ 2 ≤ ‖a‖ ^ 2) :
    Tendsto f l (𝓝 a) := by
  have hupper : Tendsto (fun i => 2 * ‖a‖ ^ 2 - 2 * inner ℝ (f i) a)
      l (𝓝 0) := by
    have hconst : Tendsto (fun _ : ι => 2 * ‖a‖ ^ 2) l (𝓝 (2 * ‖a‖ ^ 2)) :=
      tendsto_const_nhds
    have htwo : Tendsto (fun i => 2 * inner ℝ (f i) a)
        l (𝓝 (2 * ‖a‖ ^ 2)) := tendsto_const_nhds.mul hinner
    simpa only [sub_self] using hconst.sub htwo
  have hsq : Tendsto (fun i => ‖f i - a‖ ^ 2) l (𝓝 (0 : ℝ)) := by
    apply squeeze_zero' (Eventually.of_forall (fun i => sq_nonneg ‖f i - a‖))
      ?_ hupper
    filter_upwards [hbound] with i hi
    -- EP030: the real Hilbert squared-distance identity supplies the bound.
    rw [norm_sub_sq_real]
    linarith
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  have hn : Tendsto (fun i => ‖f i - a‖) l (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero]
      using hsqrt
  apply tendsto_iff_dist_tendsto_zero.mpr
  simpa only [dist_eq_norm] using hn

/-- D05.03: weak continuity of the selected pairing on the nonnegative
time domain and the supplied energy-start inequality imply a strong right
trace at s. Only that pairing, rather than full strong continuity, is assumed. -/
theorem strong_right_trace_of_energy_start
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {u : ℝ → H} {D : ℝ → ℝ} {ν s : ℝ}
    (hν : 0 ≤ ν) (hs : 0 ≤ s)
    (hD : ∀ r : ℝ, 0 ≤ r → 0 ≤ D r)
    (hweak : ContinuousOn (fun t => inner ℝ (u t) (u s)) (Ici (0 : ℝ)))
    (hE : ∀ r : ℝ, s ≤ r →
      ‖u r‖ ^ 2 + 2 * ν * (∫ q in s..r, D q) ≤ ‖u s‖ ^ 2) :
    Tendsto u (𝓝[>] s) (𝓝 (u s)) := by
  have hc := hweak s hs
  have hi : Tendsto (fun t => inner ℝ (u t) (u s))
      (𝓝[>] s) (𝓝 (inner ℝ (u s) (u s))) :=
    hc.tendsto.mono_left (nhdsWithin_mono _
      (show Ioi s ⊆ Ici (0 : ℝ) from fun t ht => hs.trans ht.le))
  -- EP029: the selected weak pairing supplies the limit, while the scalar
  -- energy inequality supplies the eventual norm bound.
  apply strong_tendsto_of_inner_and_norm_bound
  · simpa only [real_inner_self_eq_norm_sq] using hi
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact energy_le_of_energy_start hν hs hD hE ht.le

/-- D05.03 / EP031: the strong right trace becomes the zero-start trace
of the translated trajectory. -/
theorem shifted_strong_trace_of_energy_start
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {u : ℝ → H} {D : ℝ → ℝ} {ν s : ℝ}
    (hν : 0 ≤ ν) (hs : 0 ≤ s)
    (hD : ∀ r : ℝ, 0 ≤ r → 0 ≤ D r)
    (hweak : ContinuousOn (fun t => inner ℝ (u t) (u s)) (Ici (0 : ℝ)))
    (hE : ∀ r : ℝ, s ≤ r →
      ‖u r‖ ^ 2 + 2 * ν * (∫ q in s..r, D q) ≤ ‖u s‖ ^ 2) :
    Tendsto (timeTranslate s u) (𝓝[>] (0 : ℝ)) (𝓝 (u s)) := by
  -- EP031 composes the proved right trace with the translated source filter.
  have h := (strong_right_trace_of_energy_start hν hs hD hweak hE).comp
    (timeTranslate_tendsto_nhdsWithin_right s)
  simpa only [Function.comp_def, timeTranslate] using h

end

end QFA.Endpoints.Restart
