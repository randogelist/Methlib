import NSE_PAIRING_POINTWISE_LP_LIFT
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

set_option autoImplicit false

open scoped ENNReal
open MeasureTheory

noncomputable section

namespace NSEPhysicalLpDataConstruction

open H12CriticalTrilinearCompiler
open H12HolderLpAdapter
open NSEPointwisePairingIdentification
open NSEPairingPointwiseLpLift

/--
Raw physical fields with the exact integrability information required by the
critical Hölder chain.

No `Lp` representative and no norm-level pairing estimate is supplied.
-/
structure RawPhysicalFields
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) where
  J : α → Jacobian3
  u : α → RVec3
  w : α → RVec3
  J_memLp : MemLp J 3 μ
  u_memLp : MemLp u 3 μ
  w_memLp : MemLp w 3 μ
  pairing_aestronglyMeasurable :
    AEStronglyMeasurable
      (fun x => pointwisePairing (J x) (u x) (w x)) μ

/-- Pointwise product of the three physical magnitudes. -/
def tripleMagnitude
    {α : Type*} [MeasurableSpace α]
    {μ : Measure α}
    (R : RawPhysicalFields μ)
    (x : α) : ℝ :=
  ‖R.u x‖ * ‖R.J x‖ * ‖R.w x‖

/-- Actual scalar NSE pairing. -/
def pairingScalar
    {α : Type*} [MeasurableSpace α]
    {μ : Measure α}
    (R : RawPhysicalFields μ)
    (x : α) : ℝ :=
  pointwisePairing (R.J x) (R.u x) (R.w x)

/--
The product of three `L³` magnitudes belongs to `L¹`.
-/
theorem tripleMagnitude_memLp_one
    {α : Type*} [MeasurableSpace α]
    {μ : Measure α}
    (R : RawPhysicalFields μ) :
    MemLp (tripleMagnitude R) 1 μ := by
  have hUJ :
      MemLp
        (fun x => ‖R.u x‖ * ‖R.J x‖)
        p32 μ := by
    have h :=
      MemLp.mul (r := p32)
        R.J_memLp.norm
        R.u_memLp.norm
    change
      MemLp
        (fun x => ‖R.u x‖ * ‖R.J x‖)
        p32 μ at h
    exact h
  have hFinal :
      MemLp
        (fun x => (‖R.u x‖ * ‖R.J x‖) * ‖R.w x‖)
        pFinal μ := by
    have h :=
      MemLp.mul (r := pFinal)
        R.w_memLp.norm
        hUJ
    change
      MemLp
        (fun x => (‖R.u x‖ * ‖R.J x‖) * ‖R.w x‖)
        pFinal μ at h
    exact h
  change
    MemLp
      (fun x => ‖R.u x‖ * ‖R.J x‖ * ‖R.w x‖)
      1 μ
  simpa [pFinal] using hFinal

/--
The unconditional pointwise NSE theorem bounds the actual scalar pairing by
the product of physical magnitudes.
-/
theorem pairing_norm_ae_le
    {α : Type*} [MeasurableSpace α]
    {μ : Measure α}
    (R : RawPhysicalFields μ) :
    ∀ᵐ x ∂μ,
      ‖pairingScalar R x‖ ≤ tripleMagnitude R x := by
  filter_upwards [
      abs_pointwisePairing_ae μ R.J R.u R.w
    ] with x hx
  simpa [pairingScalar, tripleMagnitude, Real.norm_eq_abs] using hx

/--
The actual scalar pairing belongs to `L¹`; no pairing-integrability premise
is retained.
-/
theorem pairing_memLp_one
    {α : Type*} [MeasurableSpace α]
    {μ : Measure α}
    (R : RawPhysicalFields μ) :
    MemLp (pairingScalar R) 1 μ := by
  exact MemLp.mono'
    (tripleMagnitude_memLp_one R)
    R.pairing_aestronglyMeasurable
    (pairing_norm_ae_le R)

/-- Canonical `L³` representative of the velocity magnitude. -/
def velocityLp
    {α : Type*} [MeasurableSpace α]
    {μ : Measure α}
    (R : RawPhysicalFields μ) :
    Lp ℝ 3 μ :=
  R.u_memLp.norm.toLp (fun x => ‖R.u x‖)

/-- Canonical `L³` representative of the Jacobian operator norm. -/
def jacobianLp
    {α : Type*} [MeasurableSpace α]
    {μ : Measure α}
    (R : RawPhysicalFields μ) :
    Lp ℝ 3 μ :=
  R.J_memLp.norm.toLp (fun x => ‖R.J x‖)

/-- Canonical `L³` representative of the test-field magnitude. -/
def testLp
    {α : Type*} [MeasurableSpace α]
    {μ : Measure α}
    (R : RawPhysicalFields μ) :
    Lp ℝ 3 μ :=
  R.w_memLp.norm.toLp (fun x => ‖R.w x‖)

/-- Canonical `L¹` representative of the physical scalar pairing. -/
def pairingLp
    {α : Type*} [MeasurableSpace α]
    {μ : Measure α}
    (R : RawPhysicalFields μ) :
    Lp ℝ 1 μ :=
  (pairing_memLp_one R).toLp (pairingScalar R)

theorem velocityLp_ae
    {α : Type*} [MeasurableSpace α]
    {μ : Measure α}
    (R : RawPhysicalFields μ) :
    (fun x => velocityLp R x) =ᵐ[μ]
      (fun x => ‖R.u x‖) := by
  exact R.u_memLp.norm.coeFn_toLp

theorem jacobianLp_ae
    {α : Type*} [MeasurableSpace α]
    {μ : Measure α}
    (R : RawPhysicalFields μ) :
    (fun x => jacobianLp R x) =ᵐ[μ]
      (fun x => ‖R.J x‖) := by
  exact R.J_memLp.norm.coeFn_toLp

theorem testLp_ae
    {α : Type*} [MeasurableSpace α]
    {μ : Measure α}
    (R : RawPhysicalFields μ) :
    (fun x => testLp R x) =ᵐ[μ]
      (fun x => ‖R.w x‖) := by
  exact R.w_memLp.norm.coeFn_toLp

theorem pairingLp_ae
    {α : Type*} [MeasurableSpace α]
    {μ : Measure α}
    (R : RawPhysicalFields μ) :
    (fun x => pairingLp R x) =ᵐ[μ]
      pairingScalar R := by
  exact (pairing_memLp_one R).coeFn_toLp

/--
Critical scalar state canonically generated from raw physical fields and
chosen nonnegative critical norms `E,D`.
-/
def physicalState
    {α : Type*} [MeasurableSpace α]
    {μ : Measure α}
    (R : RawPhysicalFields μ)
    (E D : ℝ)
    (hE : 0 ≤ E)
    (hD : 0 ≤ D) :
    CriticalState where
  E := E
  D := D
  U3 := ‖velocityLp R‖
  G3 := ‖jacobianLp R‖
  L3 := ‖testLp R‖
  Iabs := ‖MeasureTheory.L1.integral (pairingLp R)‖
  E_nonneg := hE
  D_nonneg := hD
  U3_nonneg := norm_nonneg _
  G3_nonneg := norm_nonneg _
  L3_nonneg := norm_nonneg _
  Iabs_nonneg := norm_nonneg _

/--
Canonical construction of all fields in `PhysicalLpData`.
-/
def physicalLpData
    {α : Type*} [MeasurableSpace α]
    {μ : Measure α}
    (R : RawPhysicalFields μ)
    (E D : ℝ)
    (hE : 0 ≤ E)
    (hD : 0 ≤ D) :
    PhysicalLpData μ (physicalState R E D hE hD) where
  J := R.J
  u := R.u
  w := R.w
  f := velocityLp R
  g := jacobianLp R
  h := testLp R
  q := pairingLp R
  f_ae := velocityLp_ae R
  g_ae := jacobianLp_ae R
  h_ae := testLp_ae R
  q_ae := pairingLp_ae R
  U3_eq := rfl
  G3_eq := rfl
  L3_eq := rfl
  Iabs_eq := rfl

/--
Raw physical fields automatically discharge the critical Hölder endpoint.
-/
theorem criticalHolder_of_rawPhysicalFields
    {α : Type*} [MeasurableSpace α]
    {μ : Measure α}
    (R : RawPhysicalFields μ)
    (E D : ℝ)
    (hE : 0 ≤ E)
    (hD : 0 ≤ D) :
    CriticalHolder (physicalState R E D hE hD) := by
  exact criticalHolder_of_physicalLpData
    (physicalLpData R E D hE hD)

/--
Composition with the remaining periodic critical Sobolev endpoint.
-/
theorem critical_trilinear_of_rawPhysicalFields
    {α : Type*} [MeasurableSpace α]
    {μ : Measure α}
    (R : RawPhysicalFields μ)
    (E D : ℝ)
    (hE : 0 ≤ E)
    (hD : 0 ≤ D)
    (hS : PeriodicHhalfL3 (physicalState R E D hE hD)) :
    (physicalState R E D hE hD).Iabs ≤
      criticalConstant hS * E * D ^ 2 := by
  exact critical_trilinear
    (physicalState R E D hE hD)
    hS
    (criticalHolder_of_rawPhysicalFields R E D hE hD)

/--
Composition with the already audited critical absorption radius.
-/
theorem critical_trilinear_absorbed_of_rawPhysicalFields
    {α : Type*} [MeasurableSpace α]
    {μ : Measure α}
    {ν : ℝ}
    (hν : 0 < ν)
    (R : RawPhysicalFields μ)
    (E D : ℝ)
    (hE : 0 ≤ E)
    (hD : 0 ≤ D)
    (hS : PeriodicHhalfL3 (physicalState R E D hE hD))
    (hsmall :
      E ≤ H12CriticalAbsorption.criticalRadius ν
        (criticalConstant hS)) :
    (physicalState R E D hE hD).Iabs ≤
      (ν / 4) * D ^ 2 := by
  exact critical_trilinear_absorbed
    hν
    (physicalState R E D hE hD)
    hS
    (criticalHolder_of_rawPhysicalFields R E D hE hD)
    hsmall

/--
Audited root: raw `L³` physical fields construct the complete `PhysicalLpData`
object and therefore discharge `CriticalHolder`.
-/
theorem NSE_PHYSICAL_LP_DATA_CONSTRUCTION :
    ∀ {α : Type*} [MeasurableSpace α]
      {μ : Measure α}
      (R : RawPhysicalFields μ)
      (E D : ℝ)
      (hE : 0 ≤ E)
      (hD : 0 ≤ D),
      CriticalHolder (physicalState R E D hE hD) := by
  intro α inst μ R E D hE hD
  exact criticalHolder_of_rawPhysicalFields R E D hE hD

end NSEPhysicalLpDataConstruction
