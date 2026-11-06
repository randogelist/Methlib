import RH_HilbertLimit.TwoRoutes.HausdorffMeasure
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Topology.Algebra.Polynomial

/-!
# Frozen candidate C1: bounded extension of the actual xi moment functional

The predicate contains bounded real linearity and every moment identity.
Positivity is not an input.  The forward map is constructed from the retained
Hausdorff functional.  The reverse implication bounds the entire Bernstein
variation sequence by the operator norm and uses the constructed HVR criterion.

Source candidate for the external native Lean 4.33.0 compiler.
No local Lean or Lake execution; no new axiom or admitted proof.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open RH_HilbertLimit RH_HilbertLimit.TwoRoutes

namespace HXYThreeSpaces

/-- C1, frozen: the bounded dual of all continuous real functions on [0,1]. -/
def BanachExt : Prop :=
  ∃ L : C(HausdorffInterval, ℝ) →L[ℝ] ℝ,
    ∀ n : ℕ, L (intervalMonomial n) = actualNormalizedMoment n

/-- The already constructed Hausdorff functional, bundled as a linear map. -/
def hausdorffLinear (u : ℕ → ℝ) (hzero : u 0 = 1)
    (hpos : BernsteinPositive u) : C(HausdorffInterval, ℝ) →ₗ[ℝ] ℝ where
  toFun := hausdorffValue u hzero hpos
  map_add' := hausdorffValue_add u hzero hpos
  map_smul' c f := by
    simpa only [RingHom.id_apply, smul_eq_mul] using
      hausdorffValue_smul u hzero hpos c f

@[simp] theorem hausdorffLinear_apply (u : ℕ → ℝ) (hzero : u 0 = 1)
    (hpos : BernsteinPositive u) (f : C(HausdorffInterval, ℝ)) :
    hausdorffLinear u hzero hpos f = hausdorffValue u hzero hpos f := rfl

/-- Boundedness is proved; it is not an endpoint premise. -/
def hausdorffBounded (u : ℕ → ℝ) (hzero : u 0 = 1)
    (hpos : BernsteinPositive u) : C(HausdorffInterval, ℝ) →L[ℝ] ℝ :=
  (hausdorffLinear u hzero hpos).mkContinuous 1 (by
    intro f
    rw [hausdorffLinear_apply, Real.norm_eq_abs, one_mul]
    exact hausdorffValue_abs_le u hzero hpos f)

@[simp] theorem hausdorffBounded_monomial (u : ℕ → ℝ) (hzero : u 0 = 1)
    (hpos : BernsteinPositive u) (n : ℕ) :
    hausdorffBounded u hzero hpos (intervalMonomial n) = u n := by
  rw [hausdorffBounded, LinearMap.mkContinuous_apply, hausdorffLinear_apply]
  exact hausdorffValue_monomial u hzero hpos n

theorem banachExt_of_H00 (h : H00) : BanachExt := by
  exact ⟨hausdorffBounded actualNormalizedMoment
    actualNormalizedMoment_zero_unconditional (actual_bernsteinPositive_of_H00 h),
    fun n => hausdorffBounded_monomial _ _ _ n⟩

/-- Exact conditional construction: RH is the only hypothesis. -/
theorem banachExt_of_nativeRH (hRH : _root_.RiemannHypothesis) : BanachExt :=
  banachExt_of_H00 (H00_of_nativeRH hRH)

end HXYThreeSpaces
