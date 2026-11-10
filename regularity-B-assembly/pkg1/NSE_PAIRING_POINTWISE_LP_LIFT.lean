import NSE_POINTWISE_PAIRING_IDENTIFICATION
import Mathlib.MeasureTheory.Function.LpSpace.Basic

set_option autoImplicit false

open scoped ENNReal
open MeasureTheory

noncomputable section

namespace NSEPairingPointwiseLpLift

open H12CriticalTrilinearCompiler
open H12HolderLpAdapter
open NSEPointwisePairingIdentification

/--
Almost-everywhere pointwise domination lifts to the exact norm inequality
required by `NSEPairingRealization.pointwiseLift`.

The two `Lp` objects have definitionally different exponents (`1` and
`pFinal`), but `pFinal` normalizes to `1`; the comparison is performed at the
`eLpNorm` level, where no dependent transport of an indexed `Lp` object is
required.
-/
theorem lpNorm_le_tripleProduct_of_ae
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α)
    (q : Lp ℝ 1 μ)
    (f g h : Lp ℝ 3 μ)
    (hpoint :
      ∀ᵐ x ∂μ,
        ‖q x‖ ≤ ‖tripleProduct μ f g h x‖) :
    ‖q‖ ≤ ‖tripleProduct μ f g h‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  apply ENNReal.toReal_mono (by finiteness)
  have hmono :
      eLpNorm (fun x => q x) 1 μ ≤
        eLpNorm (fun x => tripleProduct μ f g h x) 1 μ :=
    eLpNorm_mono_ae (Lp.aestronglyMeasurable q) hpoint
  simpa [pFinal] using hmono

/--
Concrete state data before the norm lift.

The only inequality field is pointwise almost-everywhere domination.
There is no assumed `Lp`-norm inequality.
-/
structure PointwiseLpData
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α)
    (s : CriticalState) where
  f : Lp ℝ 3 μ
  g : Lp ℝ 3 μ
  h : Lp ℝ 3 μ
  q : Lp ℝ 1 μ
  U3_eq : s.U3 = ‖f‖
  G3_eq : s.G3 = ‖g‖
  L3_eq : s.L3 = ‖h‖
  Iabs_eq :
    s.Iabs = ‖MeasureTheory.L1.integral q‖
  pointwise :
    ∀ᵐ x ∂μ,
      ‖q x‖ ≤ ‖tripleProduct μ f g h x‖

/--
The pointwise data canonically produce the exact physical integral
realization required by the previous A-tier package.
-/
def toNSEPairingRealization
    {α : Type*} [MeasurableSpace α]
    {μ : Measure α}
    {s : CriticalState}
    (R : PointwiseLpData μ s) :
    NSEPairingRealization μ s where
  f := R.f
  g := R.g
  h := R.h
  q := R.q
  U3_eq := R.U3_eq
  G3_eq := R.G3_eq
  L3_eq := R.L3_eq
  Iabs_eq := R.Iabs_eq
  pointwiseLift :=
    lpNorm_le_tripleProduct_of_ae
      μ R.q R.f R.g R.h R.pointwise

/--
The independent norm-level premise `NSEPairingRealization.pointwiseLift`
is discharged from an almost-everywhere pointwise estimate.
-/
theorem pointwiseLift_of_ae
    {α : Type*} [MeasurableSpace α]
    {μ : Measure α}
    {s : CriticalState}
    (R : PointwiseLpData μ s) :
    ‖R.q‖ ≤ ‖tripleProduct μ R.f R.g R.h‖ :=
  lpNorm_le_tripleProduct_of_ae
    μ R.q R.f R.g R.h R.pointwise

/-- Pointwise data imply the abstract critical Hölder endpoint. -/
theorem criticalHolder_of_pointwiseLpData
    {α : Type*} [MeasurableSpace α]
    {μ : Measure α}
    {s : CriticalState}
    (R : PointwiseLpData μ s) :
    CriticalHolder s := by
  exact criticalHolder_of_nsePairing
    (toNSEPairingRealization R)

/--
Composition with the periodic critical Sobolev endpoint.
-/
theorem critical_trilinear_of_pointwiseLpData
    {α : Type*} [MeasurableSpace α]
    {μ : Measure α}
    (s : CriticalState)
    (hS : PeriodicHhalfL3 s)
    (R : PointwiseLpData μ s) :
    s.Iabs ≤ criticalConstant hS * s.E * s.D ^ 2 := by
  exact critical_trilinear_of_nsePairing
    s hS (toNSEPairingRealization R)

/--
Composition with the certified critical absorption radius.
-/
theorem critical_trilinear_absorbed_of_pointwiseLpData
    {α : Type*} [MeasurableSpace α]
    {μ : Measure α}
    {ν : ℝ}
    (hν : 0 < ν)
    (s : CriticalState)
    (hS : PeriodicHhalfL3 s)
    (R : PointwiseLpData μ s)
    (hsmall :
      s.E ≤ H12CriticalAbsorption.criticalRadius ν
        (criticalConstant hS)) :
    s.Iabs ≤ (ν / 4) * s.D ^ 2 := by
  exact critical_trilinear_absorbed_of_nsePairing
    hν s hS (toNSEPairingRealization R) hsmall

/--
Audited root: pointwise almost-everywhere domination generates the exact
`NSEPairingRealization`, with no independent norm-level lift premise.
-/
theorem NSE_PAIRING_POINTWISE_LP_LIFT :
    ∀ {α : Type*} [MeasurableSpace α]
      {μ : Measure α}
      {s : CriticalState},
      PointwiseLpData μ s →
      NSEPairingRealization μ s := by
  intro α inst μ s R
  exact toNSEPairingRealization R

end NSEPairingPointwiseLpLift
