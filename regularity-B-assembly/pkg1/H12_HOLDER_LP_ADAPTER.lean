import H12_CRITICAL_TRILINEAR_COMPILER
import Mathlib.MeasureTheory.Function.Holder

set_option autoImplicit false

open scoped ENNReal
open MeasureTheory

noncomputable section

namespace H12HolderLpAdapter

open H12CriticalTrilinearCompiler

/--
Canonical intermediate exponent generated from `3` and `3` by Hölder.
It is represented as the image of the exact real rational `3/2`.
-/
def p32 : ℝ≥0∞ :=
  ENNReal.ofReal ((3 : ℝ) / 2)

/--
Canonical final exponent obtained by combining `3/2` with another `L^3`
factor.  It is represented as the image of the exact real number `1`.
-/
def pFinal : ℝ≥0∞ :=
  ENNReal.ofReal (1 : ℝ)

/--
Real Hölder arithmetic:
  1/3 + 1/3 = 1/(3/2).
-/
theorem real_holder_33 :
    Real.HolderTriple (3 : ℝ) 3 ((3 : ℝ) / 2) := by
  constructor <;> norm_num

/--
Real Hölder arithmetic:
  1/(3/2) + 1/3 = 1.
-/
theorem real_holder_32_3 :
    Real.HolderTriple ((3 : ℝ) / 2) 3 1 := by
  constructor <;> norm_num

noncomputable instance holder33 :
    ENNReal.HolderTriple (3 : ℝ≥0∞) (3 : ℝ≥0∞) p32 := by
  simpa [p32] using real_holder_33.ennrealOfReal

noncomputable instance holderP32Three :
    ENNReal.HolderTriple p32 (3 : ℝ≥0∞) pFinal := by
  simpa [p32, pFinal] using real_holder_32_3.ennrealOfReal

/-- The canonical final exponent is exactly `1`. -/
theorem pFinal_eq_one : pFinal = 1 := by
  simp [pFinal]

/-- Normed-space side condition for `L^3`. -/
instance factThree : Fact (1 ≤ (3 : ℝ≥0∞)) :=
  ⟨by norm_num⟩

/-- Normed-space side condition for the intermediate Hölder space. -/
instance factP32 : Fact (1 ≤ p32) :=
  ⟨by
    rw [← pFinal_eq_one]
    exact ENNReal.HolderTriple.le p32 3 pFinal⟩

/-- Normed-space side condition for the final Hölder space. -/
instance factPFinal : Fact (1 ≤ pFinal) :=
  ⟨by rw [pFinal_eq_one]⟩

/--
The canonical three-factor Hölder product in `Lp`.

The first multiplication sends `L^3 × L^3` to the canonical `p32` space.
The second multiplication sends that result and another `L^3` factor to
the canonical final Hölder exponent.
-/
def tripleProduct
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α)
    (f g h : Lp ℝ 3 μ) :
    Lp ℝ pFinal μ :=
  ((f • g : Lp ℝ p32 μ) • h : Lp ℝ pFinal μ)

/--
Three-factor Hölder norm estimate derived entirely from Mathlib's
heterogeneous `Lp` scalar multiplication.
-/
theorem tripleProduct_norm_le
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α)
    (f g h : Lp ℝ 3 μ) :
    ‖tripleProduct μ f g h‖ ≤
      ‖f‖ * ‖g‖ * ‖h‖ := by
  unfold tripleProduct
  calc
    ‖((f • g : Lp ℝ p32 μ) • h : Lp ℝ pFinal μ)‖
        ≤ ‖(f • g : Lp ℝ p32 μ)‖ * ‖h‖ := by
          exact MeasureTheory.Lp.norm_smul_le
            (f := (f • g : Lp ℝ p32 μ)) (g := h)
    _ ≤ (‖f‖ * ‖g‖) * ‖h‖ := by
          exact mul_le_mul_of_nonneg_right
            (MeasureTheory.Lp.norm_smul_le (f := f) (g := g))
            (norm_nonneg h)
    _ = ‖f‖ * ‖g‖ * ‖h‖ := rfl

/--
Semantic realization of one critical NSE pairing by three `L^3` factors.

The product norm estimate is no longer assumed here; only the identification/
domination of the concrete nonlinear pairing by the canonical Hölder product
remains explicit.
-/
structure CriticalPairingRealization
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α)
    (s : CriticalState) where
  f : Lp ℝ 3 μ
  g : Lp ℝ 3 μ
  h : Lp ℝ 3 μ
  U3_eq : s.U3 = ‖f‖
  G3_eq : s.G3 = ‖g‖
  L3_eq : s.L3 = ‖h‖
  pairingDominated :
    s.Iabs ≤ ‖tripleProduct μ f g h‖

/--
A concrete `Lp` realization discharges the abstract `CriticalHolder`
premise of the critical trilinear compiler.
-/
theorem criticalHolder_of_realization
    {α : Type*} [MeasurableSpace α]
    {μ : Measure α}
    {s : CriticalState}
    (R : CriticalPairingRealization μ s) :
    CriticalHolder s := by
  unfold CriticalHolder
  calc
    s.Iabs ≤ ‖tripleProduct μ R.f R.g R.h‖ :=
      R.pairingDominated
    _ ≤ ‖R.f‖ * ‖R.g‖ * ‖R.h‖ :=
      tripleProduct_norm_le μ R.f R.g R.h
    _ = s.U3 * s.G3 * s.L3 := by
      rw [← R.U3_eq, ← R.G3_eq, ← R.L3_eq]

/--
The complete critical trilinear estimate with `CriticalHolder` removed as an
independent premise.

Only:
  * `PeriodicHhalfL3`, and
  * `CriticalPairingRealization`
remain.
-/
theorem critical_trilinear_of_realization
    {α : Type*} [MeasurableSpace α]
    {μ : Measure α}
    (s : CriticalState)
    (hS : PeriodicHhalfL3 s)
    (R : CriticalPairingRealization μ s) :
    s.Iabs ≤ criticalConstant hS * s.E * s.D ^ 2 := by
  exact critical_trilinear s hS
    (criticalHolder_of_realization R)

/--
Absorbed critical trilinear estimate with the abstract `CriticalHolder`
premise eliminated.
-/
theorem critical_trilinear_absorbed_of_realization
    {α : Type*} [MeasurableSpace α]
    {μ : Measure α}
    {ν : ℝ}
    (hν : 0 < ν)
    (s : CriticalState)
    (hS : PeriodicHhalfL3 s)
    (R : CriticalPairingRealization μ s)
    (hsmall :
      s.E ≤ H12CriticalAbsorption.criticalRadius ν
        (criticalConstant hS)) :
    s.Iabs ≤ (ν / 4) * s.D ^ 2 := by
  exact critical_trilinear_absorbed hν s hS
    (criticalHolder_of_realization R)
    hsmall

/--
Audited root: the Hölder product inequality is unconditional, and the abstract
`CriticalHolder` premise is replaced by one explicit semantic pairing
realization.
-/
theorem H12_HOLDER_LP_ADAPTER :
    ∀ {α : Type*} [MeasurableSpace α]
      {μ : Measure α}
      {s : CriticalState},
      CriticalPairingRealization μ s →
      CriticalHolder s := by
  intro α inst μ s R
  exact criticalHolder_of_realization R

end H12HolderLpAdapter
