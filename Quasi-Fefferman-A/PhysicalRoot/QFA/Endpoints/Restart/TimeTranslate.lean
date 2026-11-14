import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith

/-!
# QFA: temporal translation on restricted Lebesgue intervals

Project status: B_TIER. This file is an A_TIER_CANDIDATE only.
External compilation and theorem-level axiom audit are pending.
No local Lean or Lake execution is authorized by this file.

Proof index: QUASI_FEFFERMAN_A_ENTRYPOINT_COMPOSITION_B_TIER, version 1.2,
D05.03--D05.04 / EP031--EP035.

Selective source ports:
  repository: randogelist/Methlib
  commit: e6d7a34aba1549d098b0f8bd0caefd9dbdc85b0c
  file: Quasi-Fefferman-B/QuasiFeffermanB/TimeTranslate.lean
  source blob: 6417b89a2008f3af626819381a31d5c92fb58cd6
  declarations: timeTranslate, timeTranslate_measurePreserving_Ioc,
    timeTranslate_memLp_Ioc, timeTranslate_ae_Ioc
  file: Quasi-Fefferman-B/QuasiFeffermanB/LHRestart.lean
  source blob: 99c8781a467659b4a44da1a22f284e15f375e523
  declaration: timeTranslate_tendsto_nhdsWithin_right
  source fragment: dissipation_integrable in LH_RESTART_FROM_ENERGY_START

The generic source bodies are retained with a new namespace and specific
Mathlib imports. The target is the QFA source baseline. No QFB package
dependency, spatial domain, or PDE carrier occurs here.

Mathlib pin: db584cd6d46c92f209a44c0f1c829460d327499d.
External toolchain: leanprover/lean4:v4.33.0.

Physical trajectory applications use s >= 0 and shifted times t >= 0.
The real-valued time carrier does not extend a trajectory identity or a
singleton claim to negative times.
-/

set_option autoImplicit false
set_option Elab.async true

open Set Filter MeasureTheory
open scoped ENNReal Topology Interval

namespace QFA.Endpoints.Restart

noncomputable section

/-- Translation of a time-indexed carrier. The order `t + s` agrees with
the pinned source and with EP035. -/
def timeTranslate {E : Type*} (s : ℝ) (f : ℝ → E) : ℝ → E :=
  fun t => f (t + s)

/-- EP031 / D05.03: positive times tending to zero translate to the right
neighborhood filter at the restart time. -/
theorem timeTranslate_tendsto_nhdsWithin_right (s : ℝ) :
    Tendsto (fun t : ℝ => t + s) (𝓝[>] (0 : ℝ)) (𝓝[>] s) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have hc : Continuous (fun t : ℝ => t + s) := continuous_id.add continuous_const
    simpa only [zero_add] using
      (hc.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with t ht
    change (0 : ℝ) < t at ht
    change s < t + s
    linarith

/-- EP032 / D05.04: the exact restricted-measure translation. -/
theorem timeTranslate_measurePreserving_Ioc (s T : ℝ) :
    MeasurePreserving (fun t : ℝ => t + s)
      (volume.restrict (Ioc (0 : ℝ) T))
      (volume.restrict (Ioc s (T + s))) := by
  have hmp : MeasurePreserving (fun t : ℝ => t + s) volume volume :=
    ⟨(continuous_id.add continuous_const).measurable, map_add_right_eq_self volume s⟩
  have hpre : (fun t : ℝ => t + s) ⁻¹' Ioc s (T + s) = Ioc (0 : ℝ) T := by
    ext t
    simp only [mem_preimage, mem_Ioc]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  simpa only [hpre] using hmp.restrict_preimage (s := Ioc s (T + s)) measurableSet_Ioc

/-- EP033 / D05.04: a supplied `MemLp` class on the original positive-time
horizon restricts and translates to the restarted horizon. -/
theorem timeTranslate_memLp_Ioc
    {E : Type*} [NormedAddCommGroup E] {f : ℝ → E} {p : ℝ≥0∞}
    {s T : ℝ} (hs : 0 ≤ s)
    (hf : MemLp f p (volume.restrict (Ioc (0 : ℝ) (T + s)))) :
    MemLp (timeTranslate s f) p (volume.restrict (Ioc (0 : ℝ) T)) := by
  have hsub : Ioc s (T + s) ⊆ Ioc (0 : ℝ) (T + s) := by
    intro t ht
    exact ⟨hs.trans_lt ht.1, ht.2⟩
  -- EP032 supplies the measure-preserving map for this exact interval.
  exact (hf.mono_measure (Measure.restrict_mono_set volume hsub)).comp_measurePreserving
    (timeTranslate_measurePreserving_Ioc s T)

/-- EP034 / D05.04: transport of an almost-everywhere predicate, without
requiring measurability of the predicate's truth set. -/
theorem timeTranslate_ae_Ioc {P : ℝ → Prop} {s T : ℝ} (hs : 0 ≤ s)
    (hP : ∀ᵐ r ∂volume.restrict (Ioc (0 : ℝ) (T + s)), P r) :
    ∀ᵐ r ∂volume.restrict (Ioc (0 : ℝ) T), P (r + s) := by
  have hglobal := (ae_restrict_iff' measurableSet_Ioc).mp hP
  have hrestricted : ∀ᵐ r ∂volume.restrict (Ioc s (T + s)), P r := by
    apply (ae_restrict_iff' measurableSet_Ioc).mpr
    filter_upwards [hglobal] with r hr
    intro hrs
    exact hr ⟨hs.trans_lt hrs.1, hrs.2⟩
  -- EP032: the restricted pushforward is the translated interval measure.
  have hmp := timeTranslate_measurePreserving_Ioc s T
  have hmapped : ∀ᵐ r ∂Measure.map (fun t : ℝ => t + s)
      (volume.restrict (Ioc (0 : ℝ) T)), P r := by
    rw [hmp.map_eq]
    exact hrestricted
  exact ae_of_ae_map hmp.aemeasurable hmapped

/-- EP035 / D05.04: scalar interval-integral translation. This identity is
valid for the total Bochner integral; analytic integrability is supplied
separately by the following transport theorems. -/
theorem timeTranslate_intervalIntegral (f : ℝ → ℝ) (s a b : ℝ) :
    (∫ t in a..b, timeTranslate s f t) = ∫ t in a + s..b + s, f t := by
  -- EP035: intervalIntegral.integral_comp_add_right, at the pinned Mathlib source.
  simpa only [timeTranslate] using
    (intervalIntegral.integral_comp_add_right (a := a) (b := b) f s)

/-- Transport of actual scalar interval integrability. -/
theorem timeTranslate_intervalIntegrable
    {f : ℝ → ℝ} {s a b : ℝ}
    (hf : IntervalIntegrable f volume (a + s) (b + s)) :
    IntervalIntegrable (timeTranslate s f) volume a b := by
  -- Mathlib IntervalIntegrable.comp_add_right; the source signature retains
  -- its endpoint finiteness argument, discharged for the real codomain.
  change IntervalIntegrable (fun t : ℝ => f (t + s)) volume a b
  simpa only [add_sub_cancel_right] using hf.comp_add_right s

/-- D05.04: restriction and translation of the supplied dissipation
integrability on the original positive-time horizon. -/
theorem timeTranslate_dissipation_intervalIntegrable
    {D : ℝ → ℝ} {s T : ℝ} (hs : 0 ≤ s) (hT : 0 ≤ T)
    (hD : IntervalIntegrable D volume (0 : ℝ) (T + s)) :
    IntervalIntegrable (timeTranslate s D) volume (0 : ℝ) T := by
  -- This is the generic dissipation_integrable source fragment of
  -- LH_RESTART_FROM_ENERGY_START, with its PDE field replaced by D.
  have hI := hD.mono_set
    (show uIcc s (T + s) ⊆ uIcc (0 : ℝ) (T + s) by
      rw [uIcc_of_le (by linarith : s ≤ T + s),
        uIcc_of_le (add_nonneg hT hs)]
      exact Icc_subset_Icc hs le_rfl)
  change IntervalIntegrable (fun t : ℝ => D (t + s)) volume (0 : ℝ) T
  simpa only [sub_self, add_sub_cancel_right]
    using hI.comp_add_right s

end

end QFA.Endpoints.Restart
