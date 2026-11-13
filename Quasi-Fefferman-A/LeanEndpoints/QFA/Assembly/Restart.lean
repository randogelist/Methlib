import QFA.Endpoints.Composition.GoodTimeAndTrace
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas

/-!
# QFA: reusable restart assembly for the concrete spatial L2 profile

STATUS = A_TIER_CANDIDATE.
Mathlib pin: db584cd6d46c92f209a44c0f1c829460d327499d.
External toolchain: leanprover/lean4:v4.33.0; cached native Windows runs.
No local Lean or Lake execution. External compilation and exact declaration
axiom auditing remain pending.

Locations: D02.05, D05.02--D05.04. The assembly consumes LE052, LE061, LE062,
LE068, LE072 and LE073, together with EP011 and the inspected measurability
and continuity composition declarations named at their calls.

The output contains a shifted EnergyProfile, weak pairing continuity and a
strong shifted initial trace. Its spatial carrier remains actual full-volume
L2(R3;R3). Physical weak-gradient identification, divergence and the translated
weak momentum equation remain separate obligations. No Leray-Hopf membership,
solution existence or regularity conclusion is included in RestartData.

Every energy and trace assertion concerns nonnegative time. Negative values
of the total-real trajectory representation are auxiliary.
-/

set_option autoImplicit false
set_option Elab.async true

open MeasureTheory Set Filter
open scoped Interval Topology ENNReal

namespace QFA.Assembly.Restart

open QFA.Representation
open QFA.Endpoints.Restart

noncomputable section

/-- Translation of the supplied spatial L2 directional-field family. -/
def gradientTranslate (s : ℝ) (G : ℝ → Fin 3 → RealSpatialL2) :
    ℝ → Fin 3 → RealSpatialL2 :=
  fun t => G (t + s)

/-- The actual squared-norm energy inequality at every upper endpoint.
No admissibility, gradient or momentum predicate is inserted here. -/
def EnergyStart
    (ν : ℝ) (u : ℝ → RealSpatialL2) (G : ℝ → Fin 3 → RealSpatialL2)
    (s : ℝ) : Prop :=
  ∀ r : ℝ, s ≤ r →
    velocityEnergy (u r) + 2 * ν * (∫ q in s..r, gradientEnergy (G q)) ≤
      velocityEnergy (u s)

/-- Precisely the generic field data prepared for a later physical restart.
No field asserts the missing weak equation or the desired regularity theorem. -/
structure RestartData
    (ν : ℝ) (u : ℝ → RealSpatialL2) (G : ℝ → Fin 3 → RealSpatialL2)
    (s : ℝ) : Prop where
  profile :
    EnergyProfile ν (u s) (timeTranslate s u) (gradientTranslate s G)
  weak_pairing_continuity : ∀ b : RealSpatialL2,
    ContinuousOn (fun t => inner ℝ (timeTranslate s u t) b) (Ici (0 : ℝ))
  strong_trace :
    Tendsto (timeTranslate s u) (𝓝[>] (0 : ℝ)) (𝓝 (u s))

/-- Restricted a.e. strong measurability under a nonnegative time shift.
The source and target intervals are the same as those in LE061--LE063. -/
theorem timeTranslate_aestronglyMeasurable_Ioc
    {E : Type*} [TopologicalSpace E] {f : ℝ → E} {s T : ℝ}
    (hs : 0 ≤ s)
    (hf : AEStronglyMeasurable f (volume.restrict (Ioc (0 : ℝ) (T + s)))) :
    AEStronglyMeasurable (timeTranslate s f)
      (volume.restrict (Ioc (0 : ℝ) T)) := by
  have hsub : Ioc s (T + s) ⊆ Ioc (0 : ℝ) (T + s) := by
    intro t ht
    exact ⟨hs.trans_lt ht.1, ht.2⟩
  -- AEStronglyMeasurable.mono_measure: genuine restriction of the supplied data.
  have hrestricted :=
    hf.mono_measure (Measure.restrict_mono_set volume hsub)
  -- LE061 and AEStronglyMeasurable.comp_measurePreserving: actual pullback.
  change AEStronglyMeasurable (f ∘ (fun t : ℝ => t + s))
    (volume.restrict (Ioc (0 : ℝ) T))
  exact hrestricted.comp_measurePreserving (timeTranslate_measurePreserving_Ioc s T)

/-- EP011 converts both intervals to the null-endpoint-equivalent Ioc form. -/
theorem timeTranslate_aestronglyMeasurable_Ioo
    {E : Type*} [TopologicalSpace E] {f : ℝ → E} {s T : ℝ}
    (hs : 0 ≤ s)
    (hf : AEStronglyMeasurable f (volume.restrict (Ioo (0 : ℝ) (T + s)))) :
    AEStronglyMeasurable (timeTranslate s f)
      (volume.restrict (Ioo (0 : ℝ) T)) := by
  rw [MeasureTheory.restrict_Ioo_eq_restrict_Ioc] at hf ⊢
  exact timeTranslate_aestronglyMeasurable_Ioc hs hf

/-- EP011 and LE062 transport the actual time MemLp class on open intervals. -/
theorem timeTranslate_memLp_Ioo
    {E : Type*} [NormedAddCommGroup E] {f : ℝ → E} {p : ℝ≥0∞} {s T : ℝ}
    (hs : 0 ≤ s)
    (hf : MemLp f p (volume.restrict (Ioo (0 : ℝ) (T + s)))) :
    MemLp (timeTranslate s f) p (volume.restrict (Ioo (0 : ℝ) T)) := by
  rw [MeasureTheory.restrict_Ioo_eq_restrict_Ioc] at hf ⊢
  exact timeTranslate_memLp_Ioc hs hf

/-- Weak continuity of every selected spatial Hilbert pairing survives a
nonnegative time shift on the physical domain Ici 0. -/
theorem timeTranslate_weakPairingContinuousOn
    {u : ℝ → RealSpatialL2} {s : ℝ} (hs : 0 ≤ s)
    (hweak : ∀ b : RealSpatialL2,
      ContinuousOn (fun t => inner ℝ (u t) b) (Ici (0 : ℝ))) :
    ∀ b : RealSpatialL2,
      ContinuousOn (fun t => inner ℝ (timeTranslate s u t) b) (Ici (0 : ℝ)) := by
  intro b
  have hshift : Continuous (fun t : ℝ => t + s) := continuous_id.add continuous_const
  have hmaps : MapsTo (fun t : ℝ => t + s) (Ici (0 : ℝ)) (Ici (0 : ℝ)) := by
    intro t ht
    exact add_nonneg ht hs
  -- ContinuousOn.comp retains the domain condition through the explicit MapsTo proof.
  simpa only [Function.comp_def, timeTranslate] using
    (hweak b).comp hshift.continuousOn hmaps

/-- Assemble the complete finite-horizon EnergyProfile after a supplied
valid energy start. The shifted measurability and MemLp premises are derived;
the actual energy inequality is transported with every nonnegative endpoint. -/
theorem energyProfile_timeTranslate
    {ν s : ℝ} {a : RealSpatialL2}
    {u : ℝ → RealSpatialL2} {G : ℝ → Fin 3 → RealSpatialL2}
    (h : EnergyProfile ν a u G) (hs : 0 ≤ s)
    (hstart : EnergyStart ν u G s) :
    EnergyProfile ν (u s) (timeTranslate s u) (gradientTranslate s G) := by
  constructor
  · intro R hR
    have hRs : 0 < R + s := lt_of_lt_of_le hR (le_add_of_nonneg_right hs)
    exact timeTranslate_aestronglyMeasurable_Ioo hs
      (h.velocity_aestronglyMeasurable (R + s) hRs)
  · intro R hR j
    have hRs : 0 < R + s := lt_of_lt_of_le hR (le_add_of_nonneg_right hs)
    change MemLp (timeTranslate s (fun t : ℝ => G t j)) 2
      (volume.restrict (Ioo (0 : ℝ) R))
    exact timeTranslate_memLp_Ioo hs (h.gradient_memLp (R + s) hRs j)
  · -- LE068: no positivity of viscosity is required for the translation itself.
    have hshift := timeTranslate_energy_from_start
      (E := fun t => velocityEnergy (u t))
      (D := fun t => gradientEnergy (G t)) (ν := ν) (s := s) hstart
    simpa only [gradientTranslate, timeTranslate] using hshift

/-- The field profile, weak pairing continuity and a valid energy start
construct all three fields of RestartData. Positivity used for the strong
trace is explicit; the derivative/PDE obligations remain separate. -/
theorem restartData_of_energyStart
    {ν s : ℝ} {a : RealSpatialL2}
    {u : ℝ → RealSpatialL2} {G : ℝ → Fin 3 → RealSpatialL2}
    (h : EnergyProfile ν a u G) (hν : 0 ≤ ν) (hs : 0 ≤ s)
    (hweak : ∀ b : RealSpatialL2,
      ContinuousOn (fun t => inner ℝ (u t) b) (Ici (0 : ℝ)))
    (hstart : EnergyStart ν u G s) :
    RestartData ν u G s := by
  refine ⟨energyProfile_timeTranslate h hs hstart,
    timeTranslate_weakPairingContinuousOn hs hweak, ?_⟩
  have hE : ∀ r : ℝ, s ≤ r →
      ‖u r‖ ^ 2 + 2 * ν * (∫ q in s..r, gradientEnergy (G q)) ≤ ‖u s‖ ^ 2 := by
    simpa only [EnergyStart, velocityEnergy] using hstart
  -- LE072: all dissipation values are squared-norm sums and hence nonnegative.
  exact shifted_strong_trace_of_energy_start hν hs
    (fun r _ => gradientEnergy_nonneg (G r)) (hweak (u s)) hE

/-- Deterministic selection-to-restart-data assembly. The arbitrary Good
predicate and the all-upper-endpoint energy start remain in the witness.
The strict QFA cutoff is unchanged. This conclusion does not assert LH membership. -/
theorem exists_restartData_before
    {ν δ : ℝ} {a : RealSpatialL2}
    {u : ℝ → RealSpatialL2} {G : ℝ → Fin 3 → RealSpatialL2}
    {Good : ℝ → Prop}
    (h : EnergyProfile ν a u G) (hν : 0 < ν)
    (hcut : ‖a‖ ^ 4 / (16 * Real.pi ^ 2 * ν ^ 5) < δ)
    (hweak : ∀ b : RealSpatialL2,
      ContinuousOn (fun t => inner ℝ (u t) b) (Ici (0 : ℝ)))
    (hgood : ∀ᵐ s ∂volume.restrict (Ioo (0 : ℝ) δ),
      Good s ∧ EnergyStart ν u G s) :
    ∃ s, 0 < s ∧ s < δ ∧ Good s ∧
      velocityEnergy (u s) * gradientEnergy (G s) < 4 * Real.pi ^ 2 * ν ^ 4 ∧
      EnergyStart ν u G s ∧ RestartData ν u G s := by
  -- LE073 supplies the selected point, the unchanged energy start and strong traces.
  obtain ⟨s, hs0, hsδ, hgs, hsmall, hstart, _, htrace⟩ :=
    QFA.Endpoints.Composition.exists_subcritical_good_time_with_strong_trace
      h hν hcut hweak hgood
  have hdata : RestartData ν u G s :=
    ⟨energyProfile_timeTranslate h hs0.le hstart,
      timeTranslate_weakPairingContinuousOn hs0.le hweak, htrace⟩
  exact ⟨s, hs0, hsδ, hgs, hsmall, hstart, hdata⟩

end

end QFA.Assembly.Restart
