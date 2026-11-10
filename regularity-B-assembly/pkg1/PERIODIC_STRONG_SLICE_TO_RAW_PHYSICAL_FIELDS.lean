import NSE_PHYSICAL_LP_DATA_CONSTRUCTION

set_option autoImplicit false

open scoped ENNReal
open MeasureTheory

noncomputable section

namespace PeriodicStrongSliceToRawPhysicalFields

open H12CriticalTrilinearCompiler
open NSEPointwisePairingIdentification
open NSEPairingPointwiseLpLift
open NSEPhysicalLpDataConstruction

/-- The physical unit three-torus. -/
abbrev Torus3 := UnitAddTorus (Fin 3)

/--
One periodic strong time-slice at exactly the integrability level consumed by
the critical pairing chain.

The scalar pairing measurability is not supplied: it is derived.
-/
structure PeriodicStrongSlice where
  J : Torus3 → Jacobian3
  u : Torus3 → RVec3
  w : Torus3 → RVec3
  J_memLp :
    MemLp J 3 (volume : Measure Torus3)
  u_memLp :
    MemLp u 3 (volume : Measure Torus3)
  w_memLp :
    MemLp w 3 (volume : Measure Torus3)

/--
Application of an operator-valued measurable field to a vector-valued
measurable field remains almost-everywhere strongly measurable.
-/
theorem advection_aestronglyMeasurable
    (S : PeriodicStrongSlice) :
    AEStronglyMeasurable
      (fun x => S.J x (S.u x))
      (volume : Measure Torus3) := by
  have hpair :
      AEStronglyMeasurable
        (fun x => (S.J x, S.u x))
        (volume : Measure Torus3) :=
    S.J_memLp.aestronglyMeasurable.prodMk
      S.u_memLp.aestronglyMeasurable
  have happ :
      Continuous
        (fun p : Jacobian3 × RVec3 => p.1 p.2) :=
    continuous_fst.clm_apply continuous_snd
  exact happ.comp_aestronglyMeasurable hpair

/--
The actual scalar nonlinear pairing is almost-everywhere strongly measurable.
-/
theorem pairing_aestronglyMeasurable
    (S : PeriodicStrongSlice) :
    AEStronglyMeasurable
      (fun x =>
        pointwisePairing (S.J x) (S.u x) (S.w x))
      (volume : Measure Torus3) := by
  have hinner :
      AEStronglyMeasurable
        (fun x => inner ℝ (S.J x (S.u x)) (S.w x))
        (volume : Measure Torus3) :=
    AEStronglyMeasurable.inner
      (advection_aestronglyMeasurable S)
      S.w_memLp.aestronglyMeasurable
  simpa [pointwisePairing, advection] using hinner

/--
Canonical conversion of a periodic strong slice to the raw physical-field
interface.
-/
def toRawPhysicalFields
    (S : PeriodicStrongSlice) :
    RawPhysicalFields (volume : Measure Torus3) where
  J := S.J
  u := S.u
  w := S.w
  J_memLp := S.J_memLp
  u_memLp := S.u_memLp
  w_memLp := S.w_memLp
  pairing_aestronglyMeasurable :=
    pairing_aestronglyMeasurable S

/--
Exact structure-level endpoint.
-/
theorem periodicStrongSlice_has_rawPhysicalFields
    (S : PeriodicStrongSlice) :
    ∃ R : RawPhysicalFields (volume : Measure Torus3),
      R.J = S.J ∧
      R.u = S.u ∧
      R.w = S.w := by
  exact ⟨toRawPhysicalFields S, rfl, rfl, rfl⟩

/--
A periodic strong slice automatically discharges the critical Hölder endpoint.
-/
theorem criticalHolder_of_periodicStrongSlice
    (S : PeriodicStrongSlice)
    (E D : ℝ)
    (hE : 0 ≤ E)
    (hD : 0 ≤ D) :
    CriticalHolder
      (physicalState
        (toRawPhysicalFields S)
        E D hE hD) := by
  exact criticalHolder_of_rawPhysicalFields
    (toRawPhysicalFields S)
    E D hE hD

/--
Composition with the remaining periodic critical Sobolev endpoint.
-/
theorem critical_trilinear_of_periodicStrongSlice
    (S : PeriodicStrongSlice)
    (E D : ℝ)
    (hE : 0 ≤ E)
    (hD : 0 ≤ D)
    (hS :
      PeriodicHhalfL3
        (physicalState
          (toRawPhysicalFields S)
          E D hE hD)) :
    (physicalState
      (toRawPhysicalFields S)
      E D hE hD).Iabs
      ≤ criticalConstant hS * E * D ^ 2 := by
  exact critical_trilinear_of_rawPhysicalFields
    (toRawPhysicalFields S)
    E D hE hD hS

/--
Composition with the already audited viscosity-absorption radius.
-/
theorem critical_trilinear_absorbed_of_periodicStrongSlice
    {ν : ℝ}
    (hν : 0 < ν)
    (S : PeriodicStrongSlice)
    (E D : ℝ)
    (hE : 0 ≤ E)
    (hD : 0 ≤ D)
    (hS :
      PeriodicHhalfL3
        (physicalState
          (toRawPhysicalFields S)
          E D hE hD))
    (hsmall :
      E ≤ H12CriticalAbsorption.criticalRadius ν
        (criticalConstant hS)) :
    (physicalState
      (toRawPhysicalFields S)
      E D hE hD).Iabs
      ≤ (ν / 4) * D ^ 2 := by
  exact critical_trilinear_absorbed_of_rawPhysicalFields
    hν
    (toRawPhysicalFields S)
    E D hE hD hS hsmall

/--
Audited root: every periodic strong slice at the required `L³` level
canonically determines raw physical fields.
-/
theorem PERIODIC_STRONG_SLICE_TO_RAW_PHYSICAL_FIELDS :
    ∀ S : PeriodicStrongSlice,
      ∃ R : RawPhysicalFields (volume : Measure Torus3),
        R.J = S.J ∧
        R.u = S.u ∧
        R.w = S.w := by
  intro S
  exact periodicStrongSlice_has_rawPhysicalFields S

end PeriodicStrongSliceToRawPhysicalFields
