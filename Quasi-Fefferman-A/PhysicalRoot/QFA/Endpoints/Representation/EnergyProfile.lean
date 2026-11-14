import Mathlib
import QFA.Endpoints.Composition.GoodTimeOfEnvelope

/-!
# QFA: full-volume L2 field data to the scalar energy profile

Status: A_TIER_CANDIDATE. Matching external compilation and theorem-level
axiom audit remain pending. No Lean command has been executed locally.

Source baseline: Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`, Lean 4.33.0.
Derivation locations: D02.05 -> D04.01--D04.06 -> D05.01--D05.02.
Existing indexed source applications: EP011--EP028.
Existing local composition: LE014,
`QFA.Endpoints.Composition.exists_subcritical_good_time_of_envelope`.

The carrier is literally full-volume real-vector L2 on R3. The three supplied
L2 field trajectories `G` are candidate directional-gradient witnesses. Their
physical weak-derivative relation to `u` is not included in `EnergyProfile`.
The profile contains the time measurability/integrability data and the actual
zero-start squared-norm energy inequality used by the scalar composition.
It contains no momentum equation, divergence constraint, initial trace,
positive-time restart inequality, or assertion of Leray--Hopf membership.
The parameter `a` enters through the initial energy bound; a separate physical
construction must identify it with the initial trace of a solution.

Total-real trajectories are auxiliary representations. Every assumption and
conclusion below concerns nonnegative time or a restricted positive interval.
-/

set_option autoImplicit false
set_option Elab.async true

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Interval

namespace QFA.Representation

/-- Real three-vector L2 fields on R3 with full Lebesgue volume.
Neither the spatial domain nor the measure is periodic or restricted. -/
abbrev RealSpatialL2 :=
  Lp (EuclideanSpace ℝ (Fin 3)) 2
    (volume : Measure (EuclideanSpace ℝ (Fin 3)))

/-- Squared spatial L2 norm of the velocity field. -/
def velocityEnergy (v : RealSpatialL2) : ℝ := ‖v‖ ^ 2

/-- Sum of the three directional L2 energies. For actual weak-gradient
witnesses, this is the Frobenius gradient energy, not an operator norm. -/
def gradientEnergy (G : Fin 3 → RealSpatialL2) : ℝ :=
  ∑ j : Fin 3, ‖G j‖ ^ 2

theorem velocityEnergy_nonneg (v : RealSpatialL2) :
    0 ≤ velocityEnergy v := by
  exact sq_nonneg ‖v‖

theorem gradientEnergy_nonneg (G : Fin 3 → RealSpatialL2) :
    0 ≤ gradientEnergy G := by
  unfold gradientEnergy
  exact Finset.sum_nonneg (fun j _ => sq_nonneg ‖G j‖)

/-- D02.05: precise field-level data needed for the scalar energy argument.

Time integrability is specified on each finite positive interval. The
zero-start energy inequality is required at every nonnegative upper endpoint.
The structure is an energy-data predicate, not a definition of PDE admissibility.
-/
structure EnergyProfile
    (ν : ℝ) (a : RealSpatialL2)
    (u : ℝ → RealSpatialL2) (G : ℝ → Fin 3 → RealSpatialL2) : Prop where
  velocity_aestronglyMeasurable :
    ∀ R : ℝ, 0 < R →
      AEStronglyMeasurable u (volume.restrict (Ioo (0 : ℝ) R))
  gradient_memLp :
    ∀ R : ℝ, 0 < R → ∀ j : Fin 3,
      MemLp (fun t => G t j) 2 (volume.restrict (Ioo (0 : ℝ) R))
  zero_start_energy :
    ∀ t : ℝ, 0 ≤ t →
      velocityEnergy (u t) +
          2 * ν * (∫ r in (0 : ℝ)..t, gradientEnergy (G r)) ≤
        velocityEnergy a

/-- Squaring the norm of the actual L2-valued trajectory supplies the scalar
measurability hypothesis. No continuity of the energy readout is assumed. -/
theorem EnergyProfile.velocityEnergy_aestronglyMeasurable
    {ν R : ℝ} {a : RealSpatialL2}
    {u : ℝ → RealSpatialL2} {G : ℝ → Fin 3 → RealSpatialL2}
    (h : EnergyProfile ν a u G) (hR : 0 < R) :
    AEStronglyMeasurable (fun t => velocityEnergy (u t))
      (volume.restrict (Ioo (0 : ℝ) R)) := by
  -- D02.05: the inspected AEStronglyMeasurable.norm and .pow APIs.
  change AEStronglyMeasurable ((fun t : ℝ => ‖u t‖) ^ 2)
    (volume.restrict (Ioo (0 : ℝ) R))
  exact (h.velocity_aestronglyMeasurable R hR).norm.pow 2

/-- Coordinatewise time L2 membership of the supplied spatial L2 fields gives
genuine L1 integrability of the Frobenius energy readout. -/
theorem EnergyProfile.gradientEnergy_integrable
    {ν R : ℝ} {a : RealSpatialL2}
    {u : ℝ → RealSpatialL2} {G : ℝ → Fin 3 → RealSpatialL2}
    (h : EnergyProfile ν a u G) (hR : 0 < R) :
    Integrable (fun t => gradientEnergy (G t))
      (volume.restrict (Ioo (0 : ℝ) R)) := by
  -- D02.05: MemLp.integrable_norm_pow with p=2, then the exact finite sum.
  have hcoord : ∀ j : Fin 3,
      Integrable (fun t : ℝ => ‖G t j‖ ^ 2)
        (volume.restrict (Ioo (0 : ℝ) R)) := by
    intro j
    exact (h.gradient_memLp R hR j).integrable_norm_pow
      (p := 2) (by norm_num)
  simpa only [gradientEnergy] using
    (MeasureTheory.integrable_finsetSum
      (μ := volume.restrict (Ioo (0 : ℝ) R))
      (Finset.univ : Finset (Fin 3))
      (f := fun j : Fin 3 => fun t : ℝ => ‖G t j‖ ^ 2)
      (fun j _ => hcoord j))

/-- EP011--EP012 / D04.01: convert the open-set time integrability statement
into the oriented interval interface used by the AC-envelope theorem. -/
theorem EnergyProfile.gradientEnergy_intervalIntegrable
    {ν R : ℝ} {a : RealSpatialL2}
    {u : ℝ → RealSpatialL2} {G : ℝ → Fin 3 → RealSpatialL2}
    (h : EnergyProfile ν a u G) (hR : 0 < R) :
    IntervalIntegrable (fun t => gradientEnergy (G t)) volume (0 : ℝ) R := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hR.le).mpr
  change Integrable (fun t => gradientEnergy (G t))
    (volume.restrict (Ioc (0 : ℝ) R))
  rw [← MeasureTheory.restrict_Ioo_eq_restrict_Ioc]
  exact h.gradientEnergy_integrable hR

/-- D04.01: the actual zero-start energy inequality gives the envelope bound
for the actual squared L2 velocity norm at every nonnegative time. -/
theorem EnergyProfile.velocityEnergy_le_envelope
    {ν : ℝ} {a : RealSpatialL2}
    {u : ℝ → RealSpatialL2} {G : ℝ → Fin 3 → RealSpatialL2}
    (h : EnergyProfile ν a u G) {t : ℝ} (ht : 0 ≤ t) :
    velocityEnergy (u t) ≤
      QFA.Energy.envelope ‖a‖ ν (fun r => gradientEnergy (G r)) t := by
  have he := h.zero_start_energy t ht
  change velocityEnergy (u t) +
      2 * ν * (∫ r in (0 : ℝ)..t, gradientEnergy (G r)) ≤ ‖a‖ ^ 2 at he
  change velocityEnergy (u t) ≤
    ‖a‖ ^ 2 - 2 * ν * (∫ r in (0 : ℝ)..t, gradientEnergy (G r))
  linarith only [he]

/-- The all-time energy inequality supplies the a.e. scalar envelope premise
on any open positive-time observation interval. -/
theorem EnergyProfile.velocityEnergy_le_envelope_ae
    {ν R : ℝ} {a : RealSpatialL2}
    {u : ℝ → RealSpatialL2} {G : ℝ → Fin 3 → RealSpatialL2}
    (h : EnergyProfile ν a u G) :
    ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) R),
      velocityEnergy (u t) ≤
        QFA.Energy.envelope ‖a‖ ν (fun r => gradientEnergy (G r)) t := by
  have htime : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) R),
      t ∈ Ioo (0 : ℝ) R :=
    ae_restrict_mem measurableSet_Ioo
  filter_upwards [htime] with t ht
  exact h.velocityEnergy_le_envelope ht.1.le

/-- EP011--EP027 / D02.05--D04.06: product budget for actual full-volume
spatial L2 norms, retaining genuine time integrability of the product. -/
theorem EnergyProfile.energy_product_budget_Ioo
    {ν R : ℝ} {a : RealSpatialL2}
    {u : ℝ → RealSpatialL2} {G : ℝ → Fin 3 → RealSpatialL2}
    (h : EnergyProfile ν a u G) (hν : 0 < ν) (hR : 0 < R) :
    Integrable (fun t => velocityEnergy (u t) * gradientEnergy (G t))
        (volume.restrict (Ioo (0 : ℝ) R)) ∧
      (∫ t in Ioo (0 : ℝ) R, velocityEnergy (u t) * gradientEnergy (G t)) ≤
        ‖a‖ ^ 4 / (4 * ν) := by
  have hDnn : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) R),
      0 ≤ gradientEnergy (G t) :=
    Filter.Eventually.of_forall (fun t => gradientEnergy_nonneg (G t))
  have hEnn : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) R),
      0 ≤ velocityEnergy (u t) :=
    Filter.Eventually.of_forall (fun t => velocityEnergy_nonneg (u t))
  exact QFA.Energy.product_budget_Ioo
    (E := fun t => velocityEnergy (u t))
    (D := fun t => gradientEnergy (G t)) (M := ‖a‖) (ν := ν) (R := R)
    hR.le hν (h.gradientEnergy_intervalIntegrable hR)
    (h.velocityEnergy_aestronglyMeasurable hR) hDnn hEnn
    (h.velocityEnergy_le_envelope_ae (R := R))

/-- D02.05 -> LE014 / D04--D05: the field-data profile supplies every scalar
premise of the exact-cutoff good-time composition. `Good` is retained in the
witness. The conclusion alone asserts neither a physical derivative relation
for `G` nor H1 membership, a restart equation, or solution regularity. -/
theorem EnergyProfile.exists_subcritical_good_time
    {ν δ : ℝ} {a : RealSpatialL2}
    {u : ℝ → RealSpatialL2} {G : ℝ → Fin 3 → RealSpatialL2}
    {Good : ℝ → Prop}
    (h : EnergyProfile ν a u G) (hν : 0 < ν)
    (hcut : ‖a‖ ^ 4 / (16 * Real.pi ^ 2 * ν ^ 5) < δ)
    (hgood : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) δ), Good t) :
    ∃ s, 0 < s ∧ s < δ ∧ Good s ∧
      velocityEnergy (u s) * gradientEnergy (G s) < 4 * Real.pi ^ 2 * ν ^ 4 := by
  have hδ : 0 < δ :=
    lt_of_le_of_lt (QFA.Endpoints.GoodTime.qfa_cutoff_nonneg ‖a‖ hν) hcut
  have hDnn : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) δ),
      0 ≤ gradientEnergy (G t) :=
    Filter.Eventually.of_forall (fun t => gradientEnergy_nonneg (G t))
  have hEnn : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) δ),
      0 ≤ velocityEnergy (u t) :=
    Filter.Eventually.of_forall (fun t => velocityEnergy_nonneg (u t))
  -- LE014: EP011--EP027 supplies the budget; EP028 retains Good in selection.
  exact QFA.Endpoints.Composition.exists_subcritical_good_time_of_envelope
    (E := fun t => velocityEnergy (u t))
    (D := fun t => gradientEnergy (G t)) (Good := Good) (M := ‖a‖)
    (ν := ν) (δ := δ) hν hcut (h.gradientEnergy_intervalIntegrable hδ)
    (h.velocityEnergy_aestronglyMeasurable hδ) hDnn hEnn
    (h.velocityEnergy_le_envelope_ae (R := δ)) hgood

end QFA.Representation
