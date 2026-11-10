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
The canonical Hölder product agrees almost everywhere with the pointwise
three-factor product at the level of norms.
-/
theorem tripleProduct_norm_ae
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α)
    (f g h : Lp ℝ 3 μ) :
    ∀ᵐ x ∂μ,
      ‖tripleProduct μ f g h x‖ =
        ‖f x‖ * ‖g x‖ * ‖h x‖ := by
  filter_upwards [
      Lp.coeFn_lpSMul (r := p32) f g,
      Lp.coeFn_lpSMul (r := pFinal)
        (f • g : Lp ℝ p32 μ) h
    ] with x hfg hfinal
  have hfg' :
      (f • g : Lp ℝ p32 μ) x = f x * g x := by
    simpa [smul_eq_mul] using hfg
  have hfinal' :
      tripleProduct μ f g h x =
        (f • g : Lp ℝ p32 μ) x * h x := by
    change
      (((f • g : Lp ℝ p32 μ) • h : Lp ℝ pFinal μ) x) =
        (f • g : Lp ℝ p32 μ) x * h x
    simpa [smul_eq_mul] using hfinal
  rw [hfinal', hfg', norm_mul, norm_mul]

/--
Almost-everywhere pointwise domination lifts to the exact norm field required
by `NSEPairingRealization.pointwiseLift`.

The exponent normalization is performed only inside `eLpNorm`; no dependent
cast between `Lp ℝ 1 μ` and `Lp ℝ pFinal μ` is introduced.
-/
theorem pointwiseLift_of_ae
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α)
    (f g h : Lp ℝ 3 μ)
    (q : Lp ℝ 1 μ)
    (hpoint :
      ∀ᵐ x ∂μ,
        ‖q x‖ ≤ ‖f x‖ * ‖g x‖ * ‖h x‖) :
    ‖q‖ ≤ ‖tripleProduct μ f g h‖ := by
  have htriple :
      ∀ᵐ x ∂μ,
        ‖q x‖ ≤ ‖tripleProduct μ f g h x‖ := by
    filter_upwards [hpoint, tripleProduct_norm_ae μ f g h]
      with x hq hprod
    rw [hprod]
    exact hq
  rw [Lp.norm_def, Lp.norm_def]
  refine ENNReal.toReal_mono (by finiteness) ?_
  have hE :
      eLpNorm (fun x => q x) (1 : ℝ≥0∞) μ ≤
        eLpNorm (fun x => tripleProduct μ f g h x)
          (1 : ℝ≥0∞) μ :=
    eLpNorm_mono_ae
      (p := (1 : ℝ≥0∞)) (μ := μ) htriple
  simpa [pFinal] using hE

/--
Physical `Lp` representatives of one NSE nonlinear pairing.

The almost-everywhere equalities identify:
  * `f` with the velocity magnitude;
  * `g` with the Jacobian operator norm;
  * `h` with the test-field magnitude;
  * `q` with the actual scalar pointwise pairing.

No norm inequality is included as a field.
-/
structure PhysicalLpData
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α)
    (s : CriticalState) where
  J : α → Jacobian3
  u : α → RVec3
  w : α → RVec3
  f : Lp ℝ 3 μ
  g : Lp ℝ 3 μ
  h : Lp ℝ 3 μ
  q : Lp ℝ 1 μ
  f_ae :
    (fun x => f x) =ᵐ[μ] (fun x => ‖u x‖)
  g_ae :
    (fun x => g x) =ᵐ[μ] (fun x => ‖J x‖)
  h_ae :
    (fun x => h x) =ᵐ[μ] (fun x => ‖w x‖)
  q_ae :
    (fun x => q x) =ᵐ[μ]
      (fun x => pointwisePairing (J x) (u x) (w x))
  U3_eq : s.U3 = ‖f‖
  G3_eq : s.G3 = ‖g‖
  L3_eq : s.L3 = ‖h‖
  Iabs_eq :
    s.Iabs = ‖MeasureTheory.L1.integral q‖

/--
The unconditional finite-dimensional pointwise theorem supplies the
almost-everywhere scalar-product bound for the chosen `Lp` representatives.
-/
theorem physical_pointwise_bound
    {α : Type*} [MeasurableSpace α]
    {μ : Measure α}
    {s : CriticalState}
    (R : PhysicalLpData μ s) :
    ∀ᵐ x ∂μ,
      ‖R.q x‖ ≤ ‖R.f x‖ * ‖R.g x‖ * ‖R.h x‖ := by
  filter_upwards [
      R.q_ae,
      R.f_ae,
      R.g_ae,
      R.h_ae,
      abs_pointwisePairing_ae μ R.J R.u R.w
    ] with x hq hf hg hh hp
  calc
    ‖R.q x‖ =
        |pointwisePairing (R.J x) (R.u x) (R.w x)| := by
      rw [hq, Real.norm_eq_abs]
    _ ≤ ‖R.u x‖ * ‖R.J x‖ * ‖R.w x‖ := hp
    _ = ‖R.f x‖ * ‖R.g x‖ * ‖R.h x‖ := by
      rw [hf, hg, hh]
      simp

/--
Construction of the already A-tier `NSEPairingRealization`, with
`pointwiseLift` now derived rather than supplied.
-/
def toNSEPairingRealization
    {α : Type*} [MeasurableSpace α]
    {μ : Measure α}
    {s : CriticalState}
    (R : PhysicalLpData μ s) :
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
    pointwiseLift_of_ae μ R.f R.g R.h R.q
      (physical_pointwise_bound R)

/--
The physical `Lp` representative data therefore discharge `CriticalHolder`.
-/
theorem criticalHolder_of_physicalLpData
    {α : Type*} [MeasurableSpace α]
    {μ : Measure α}
    {s : CriticalState}
    (R : PhysicalLpData μ s) :
    CriticalHolder s := by
  exact criticalHolder_of_nsePairing
    (toNSEPairingRealization R)

/--
Composition with the remaining periodic critical Sobolev endpoint.
-/
theorem critical_trilinear_of_physicalLpData
    {α : Type*} [MeasurableSpace α]
    {μ : Measure α}
    (s : CriticalState)
    (hS : PeriodicHhalfL3 s)
    (R : PhysicalLpData μ s) :
    s.Iabs ≤ criticalConstant hS * s.E * s.D ^ 2 := by
  exact critical_trilinear s hS
    (criticalHolder_of_physicalLpData R)

/--
Composition with the already A-tier viscosity absorption radius.
-/
theorem critical_trilinear_absorbed_of_physicalLpData
    {α : Type*} [MeasurableSpace α]
    {μ : Measure α}
    {ν : ℝ}
    (hν : 0 < ν)
    (s : CriticalState)
    (hS : PeriodicHhalfL3 s)
    (R : PhysicalLpData μ s)
    (hsmall :
      s.E ≤ H12CriticalAbsorption.criticalRadius ν
        (criticalConstant hS)) :
    s.Iabs ≤ (ν / 4) * s.D ^ 2 := by
  exact critical_trilinear_absorbed hν s hS
    (criticalHolder_of_physicalLpData R)
    hsmall

/--
Audited root: physical pointwise identifications imply the exact norm-level
`pointwiseLift`, hence `CriticalHolder`.
-/
theorem NSE_PAIRING_POINTWISE_LP_LIFT :
    ∀ {α : Type*} [MeasurableSpace α]
      {μ : Measure α}
      {s : CriticalState},
      PhysicalLpData μ s →
      CriticalHolder s := by
  intro α inst μ s R
  exact criticalHolder_of_physicalLpData R

end NSEPairingPointwiseLpLift
