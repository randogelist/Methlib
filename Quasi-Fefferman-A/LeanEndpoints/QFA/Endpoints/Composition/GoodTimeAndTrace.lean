import QFA.Endpoints.Representation.EnergyProfile
import QFA.Endpoints.Restart.HilbertTrace

/-!
# QFA whole-space L2 profile: selected time and strong traces

Derivation locations: D02.05 -> D04 -> D05.02-D05.03.
Existing entrypoints: scalar composition LE014, Hilbert trace EP029-EP030,
and right-time translation EP031. Local declarations remain A_TIER_CANDIDATE.

The carrier is full-volume real spatial L2 on R^3. The energy profile and
the almost-everywhere energy-start premise are explicitly retained. The
weak-gradient relation, incompressibility and momentum equation are separate
physical obligations; this theorem does not declare Leray-Hopf membership.

All time functions below may have auxiliary values at negative real times.
Every energy, trace and witness conclusion is restricted to nonnegative time.
-/

set_option autoImplicit false
set_option Elab.async true

open MeasureTheory Set Filter
open scoped Interval Topology

namespace QFA.Endpoints.Composition

/-- Full-volume energy profile plus almost-everywhere energy starts supplies
a subcritical time, its energy-start inequality, and both strong trace forms.
No scalar product-budget inequality or norm-continuity premise is assumed.
-/
theorem exists_subcritical_good_time_with_strong_trace
    {ν δ : ℝ} {a : QFA.Representation.RealSpatialL2}
    {u : ℝ → QFA.Representation.RealSpatialL2}
    {G : ℝ → Fin 3 → QFA.Representation.RealSpatialL2}
    {Good : ℝ → Prop}
    (h : QFA.Representation.EnergyProfile ν a u G)
    (hν : 0 < ν)
    (hcut : ‖a‖ ^ 4 / (16 * Real.pi ^ 2 * ν ^ 5) < δ)
    (hweak : ∀ b : QFA.Representation.RealSpatialL2,
      ContinuousOn (fun t => inner ℝ (u t) b) (Ici (0 : ℝ)))
    (hgood : ∀ᵐ s ∂volume.restrict (Ioo (0 : ℝ) δ),
      Good s ∧ ∀ r : ℝ, s ≤ r →
        QFA.Representation.velocityEnergy (u r) +
          2 * ν * (∫ q in s..r, QFA.Representation.gradientEnergy (G q)) ≤
            QFA.Representation.velocityEnergy (u s)) :
    ∃ s, 0 < s ∧ s < δ ∧ Good s ∧
      QFA.Representation.velocityEnergy (u s) *
        QFA.Representation.gradientEnergy (G s) < 4 * Real.pi ^ 2 * ν ^ 4 ∧
      (∀ r : ℝ, s ≤ r →
        QFA.Representation.velocityEnergy (u r) +
          2 * ν * (∫ q in s..r, QFA.Representation.gradientEnergy (G q)) ≤
            QFA.Representation.velocityEnergy (u s)) ∧
      Tendsto u (𝓝[>] s) (𝓝 (u s)) ∧
      Tendsto (QFA.Endpoints.Restart.timeTranslate s u)
        (𝓝[>] (0 : ℝ)) (𝓝 (u s)) := by
  -- D02.05, D04 and D05.02: all profile-to-scalar adapters are explicit.
  obtain ⟨s, hs0, hsδ, hgs, hsmall⟩ :=
    h.exists_subcritical_good_time hν hcut hgood
  have hE : ∀ r : ℝ, s ≤ r →
      ‖u r‖ ^ 2 + 2 * ν *
        (∫ q in s..r, QFA.Representation.gradientEnergy (G q)) ≤ ‖u s‖ ^ 2 := by
    simpa only [QFA.Representation.velocityEnergy] using hgs.2
  have hD : ∀ r : ℝ, 0 ≤ r →
      0 ≤ QFA.Representation.gradientEnergy (G r) :=
    fun r _ => QFA.Representation.gradientEnergy_nonneg (G r)
  -- D05.03 / EP029-EP030: weak pairing continuity plus energy gives strong trace.
  have htrace := QFA.Endpoints.Restart.strong_right_trace_of_energy_start
    hν.le hs0.le hD (hweak (u s)) hE
  -- D05.03 / EP031: the same trace expressed at the shifted initial time.
  have hshift := QFA.Endpoints.Restart.shifted_strong_trace_of_energy_start
    hν.le hs0.le hD (hweak (u s)) hE
  exact ⟨s, hs0, hsδ, hgs.1, hsmall, hgs.2, htrace, hshift⟩

end QFA.Endpoints.Composition
