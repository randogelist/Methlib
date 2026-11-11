import H12_HOLDER_LP_ADAPTER
import Mathlib.MeasureTheory.Integral.Bochner.L1

set_option autoImplicit false

open scoped ENNReal
open MeasureTheory

noncomputable section

namespace H12CriticalPairingIntegral

open H12CriticalTrilinearCompiler
open H12HolderLpAdapter

/--
The already A-tier three-factor product has exponent `pFinal`; because
`pFinal = 1`, its underlying function is genuinely `MemLp` at exponent `1`.

Crucially, the exponent equality is rewritten only in the proposition
`MemLp ... pFinal μ`, not in the indexed `Lp` type itself.
-/
theorem tripleProduct_memLp_one
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α)
    (f g h : Lp ℝ 3 μ) :
    MemLp (fun x => tripleProduct μ f g h x) 1 μ := by
  simpa [pFinal] using
    (Lp.memLp (tripleProduct μ f g h))

/--
Canonical `L^1` representative of the already A-tier three-factor product.
-/
def tripleProductOne
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α)
    (f g h : Lp ℝ 3 μ) :
    Lp ℝ 1 μ :=
  (tripleProduct_memLp_one μ f g h).toLp
    (fun x => tripleProduct μ f g h x)

/--
Passing through `MemLp.toLp` at exponent `1` preserves the norm of the
original `pFinal` product because `pFinal` is exactly `1`.
-/
theorem tripleProductOne_norm_eq
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α)
    (f g h : Lp ℝ 3 μ) :
    ‖tripleProductOne μ f g h‖ =
      ‖tripleProduct μ f g h‖ := by
  unfold tripleProductOne
  rw [Lp.norm_toLp, Lp.norm_def]
  simp [pFinal]

/-- The direct `L^1` three-factor Hölder estimate. -/
theorem tripleProductOne_norm_le
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α)
    (f g h : Lp ℝ 3 μ) :
    ‖tripleProductOne μ f g h‖ ≤
      ‖f‖ * ‖g‖ * ‖h‖ := by
  rw [tripleProductOne_norm_eq μ f g h]
  exact tripleProduct_norm_le μ f g h

/-- Actual Bochner integral of the canonical `L^1` triple product. -/
def tripleIntegral
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α)
    (f g h : Lp ℝ 3 μ) : ℝ :=
  MeasureTheory.L1.integral (tripleProductOne μ f g h)

/--
The actual integral pairing is bounded by the `L^1` norm, hence by the
three `L^3` norms.
-/
theorem tripleIntegral_norm_le
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α)
    (f g h : Lp ℝ 3 μ) :
    ‖tripleIntegral μ f g h‖ ≤
      ‖f‖ * ‖g‖ * ‖h‖ := by
  calc
    ‖tripleIntegral μ f g h‖
        ≤ ‖tripleProductOne μ f g h‖ := by
          exact MeasureTheory.L1.norm_integral_le
            (tripleProductOne μ f g h)
    _ ≤ ‖f‖ * ‖g‖ * ‖h‖ :=
      tripleProductOne_norm_le μ f g h

/--
Concrete integral realization of a critical state.

Only the identification of the scalar state entries with the actual `L^3`
norms and the actual integral pairing is required.
-/
structure CriticalIntegralRealization
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α)
    (s : CriticalState) where
  f : Lp ℝ 3 μ
  g : Lp ℝ 3 μ
  h : Lp ℝ 3 μ
  U3_eq : s.U3 = ‖f‖
  G3_eq : s.G3 = ‖g‖
  L3_eq : s.L3 = ‖h‖
  Iabs_eq : s.Iabs = ‖tripleIntegral μ f g h‖

/--
The actual integral realization automatically supplies the abstract
`CriticalHolder` premise.
-/
theorem criticalHolder_of_integralRealization
    {α : Type*} [MeasurableSpace α]
    {μ : Measure α}
    {s : CriticalState}
    (R : CriticalIntegralRealization μ s) :
    CriticalHolder s := by
  unfold CriticalHolder
  calc
    s.Iabs = ‖tripleIntegral μ R.f R.g R.h‖ := R.Iabs_eq
    _ ≤ ‖R.f‖ * ‖R.g‖ * ‖R.h‖ :=
      tripleIntegral_norm_le μ R.f R.g R.h
    _ = s.U3 * s.G3 * s.L3 := by
      rw [← R.U3_eq, ← R.G3_eq, ← R.L3_eq]

/--
Critical trilinear estimate from an actual integral realization and the
periodic Sobolev endpoint.
-/
theorem critical_trilinear_of_integralRealization
    {α : Type*} [MeasurableSpace α]
    {μ : Measure α}
    (s : CriticalState)
    (hS : PeriodicHhalfL3 s)
    (R : CriticalIntegralRealization μ s) :
    s.Iabs ≤ criticalConstant hS * s.E * s.D ^ 2 := by
  exact critical_trilinear s hS
    (criticalHolder_of_integralRealization R)

/--
Absorbed critical trilinear estimate from an actual integral realization.
-/
theorem critical_trilinear_absorbed_of_integralRealization
    {α : Type*} [MeasurableSpace α]
    {μ : Measure α}
    {ν : ℝ}
    (hν : 0 < ν)
    (s : CriticalState)
    (hS : PeriodicHhalfL3 s)
    (R : CriticalIntegralRealization μ s)
    (hsmall :
      s.E ≤ H12CriticalAbsorption.criticalRadius ν
        (criticalConstant hS)) :
    s.Iabs ≤ (ν / 4) * s.D ^ 2 := by
  exact critical_trilinear_absorbed hν s hS
    (criticalHolder_of_integralRealization R)
    hsmall

/--
Root theorem: an actual `L^1` integral realization discharges
`CriticalHolder` without any additional analytic inequality premise.
-/
theorem H12_CRITICAL_PAIRING_INTEGRAL :
    ∀ {α : Type*} [MeasurableSpace α]
      {μ : Measure α}
      {s : CriticalState},
      CriticalIntegralRealization μ s →
      CriticalHolder s := by
  intro α inst μ s R
  exact criticalHolder_of_integralRealization R

end H12CriticalPairingIntegral

