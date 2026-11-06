import RH_HilbertLimit.TwoRoutes.HausdorffMeasure
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# Frozen candidate C2: a positive-contraction Hilbert realization

The moments are the actual `RH_HilbertLimit.actualNormalizedMoment` values.
The forward construction uses the existing actual Hausdorff measure on [0,1],
complex L2, multiplication by the coordinate, and the constant unit vector.
The reverse implication is independently compiled in `HXYThreeSpaces.Hilbert`.

Source preparation only. No local Lean/Lake execution. Promotion requires the
matching external Lean 4.33.0 compilation and theorem-level axiom audit.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter RH_HilbertLimit RH_HilbertLimit.TwoRoutes
open scoped BigOperators Topology ComplexConjugate InnerProductSpace

namespace HXYThreeSpaces

/-- Exact C2. Positivity of `T` and `1 - T` is the Loewner condition
`0 <= T <= I`; every actual moment is matched. -/
def HilbertRep : Prop :=
  ∃ (H : Type) (instNorm : NormedAddCommGroup H),
    letI := instNorm
    ∃ instInner : InnerProductSpace ℂ H,
      letI := instInner
      ∃ instComplete : CompleteSpace H,
        letI := instComplete
        ∃ (T : H →L[ℂ] H) (v : H),
          IsSelfAdjoint T ∧ T.IsPositive ∧ (1 - T).IsPositive ∧
          ‖v‖ = 1 ∧
          ∀ n : ℕ, inner ℂ v ((T ^ n) v) = (actualNormalizedMoment n : ℂ)

abbrev HausdorffL2 (σ : Measure HausdorffInterval) := Lp ℂ 2 σ

section Multiplication

variable (σ : Measure HausdorffInterval)
variable (a : C(HausdorffInterval, ℝ)) (ha : ∀ q, |a q| ≤ 1)

include ha in
private theorem realMultiplier_memLp (f : HausdorffL2 σ) :
    MemLp (fun q => (a q : ℂ) * f q) 2 σ := by
  apply (Lp.memLp f).of_le
  · exact ((Complex.continuous_ofReal.comp a.continuous).aestronglyMeasurable).mul
      (Lp.aestronglyMeasurable f)
  · apply Filter.Eventually.of_forall
    intro q
    calc
      ‖(a q : ℂ) * f q‖ = |a q| * ‖f q‖ := by
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ 1 * ‖f q‖ := mul_le_mul_of_nonneg_right (ha q) (norm_nonneg _)
      _ = ‖f q‖ := one_mul _

private def realMultiplierValue (f : HausdorffL2 σ) : HausdorffL2 σ :=
  (realMultiplier_memLp σ a ha f).toLp (fun q => (a q : ℂ) * f q)

private theorem realMultiplierValue_ae (f : HausdorffL2 σ) :
    realMultiplierValue σ a ha f =ᵐ[σ] fun q => (a q : ℂ) * f q :=
  (realMultiplier_memLp σ a ha f).coeFn_toLp

private theorem realMultiplierValue_add (f g : HausdorffL2 σ) :
    realMultiplierValue σ a ha (f + g) =
      realMultiplierValue σ a ha f + realMultiplierValue σ a ha g := by
  apply Lp.ext
  filter_upwards [realMultiplierValue_ae σ a ha (f + g),
    realMultiplierValue_ae σ a ha f, realMultiplierValue_ae σ a ha g,
    Lp.coeFn_add f g,
    Lp.coeFn_add (realMultiplierValue σ a ha f) (realMultiplierValue σ a ha g)]
    with q hsum hf hg hfg hout
  simp only [Pi.add_apply] at hfg hout
  rw [hsum, hout, hf, hg, hfg, mul_add]

private theorem realMultiplierValue_smul (c : ℂ) (f : HausdorffL2 σ) :
    realMultiplierValue σ a ha (c • f) = c • realMultiplierValue σ a ha f := by
  apply Lp.ext
  filter_upwards [realMultiplierValue_ae σ a ha (c • f),
    realMultiplierValue_ae σ a ha f, Lp.coeFn_smul c f,
    Lp.coeFn_smul c (realMultiplierValue σ a ha f)]
    with q hsmul hf hcf hout
  simp only [Pi.smul_apply, smul_eq_mul] at hcf hout
  rw [hsmul, hout, hf, hcf]
  ring

private theorem realMultiplierValue_norm_le (f : HausdorffL2 σ) :
    ‖realMultiplierValue σ a ha f‖ ≤ ‖f‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [realMultiplierValue_ae σ a ha f] with q hq
  rw [hq, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_right (ha q) (norm_nonneg _)).trans_eq (one_mul _)

private def realMultiplierLinear : HausdorffL2 σ →ₗ[ℂ] HausdorffL2 σ where
  toFun := realMultiplierValue σ a ha
  map_add' := realMultiplierValue_add σ a ha
  map_smul' := realMultiplierValue_smul σ a ha

private theorem realMultiplierLinear_apply (f : HausdorffL2 σ) :
    realMultiplierLinear σ a ha f = realMultiplierValue σ a ha f := rfl

/-- Multiplication by a real continuous function bounded in absolute value by 1. -/
def realMultiplier : HausdorffL2 σ →L[ℂ] HausdorffL2 σ :=
  (realMultiplierLinear σ a ha).mkContinuous 1 fun f => by
    rw [realMultiplierLinear_apply, one_mul]
    exact realMultiplierValue_norm_le σ a ha f

theorem realMultiplier_ae (f : HausdorffL2 σ) :
    realMultiplier σ a ha f =ᵐ[σ] fun q => (a q : ℂ) * f q :=
  realMultiplierValue_ae σ a ha f

theorem realMultiplier_norm_le (f : HausdorffL2 σ) :
    ‖realMultiplier σ a ha f‖ ≤ ‖f‖ :=
  realMultiplierValue_norm_le σ a ha f

theorem realMultiplier_symmetric : (realMultiplier σ a ha).IsSymmetric := by
  intro f g
  change inner ℂ (realMultiplier σ a ha f) g =
    inner ℂ f (realMultiplier σ a ha g)
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [realMultiplier_ae σ a ha f, realMultiplier_ae σ a ha g]
    with q hf hg
  rw [hf, hg]
  change inner ℂ ((a q : ℂ) • f q) (g q) =
    inner ℂ (f q) ((a q : ℂ) • g q)
  simp [inner_smul_left, inner_smul_right] <;> ring

theorem realMultiplier_positive (ha0 : ∀ q, 0 ≤ a q) :
    (realMultiplier σ a ha).IsPositive := by
  refine ⟨realMultiplier_symmetric σ a ha, ?_⟩
  intro f
  change 0 ≤ (inner ℂ (realMultiplier σ a ha f) f).re
  rw [L2.inner_def]
  have hreal :=
    integral_re (L2.integrable_inner (𝕜 := ℂ) (realMultiplier σ a ha f) f)
  simp only [RCLike.re_to_complex] at hreal
  rw [← hreal]
  apply MeasureTheory.integral_nonneg_of_ae
  filter_upwards [realMultiplier_ae σ a ha f] with q hq
  rw [hq]
  change 0 ≤ (inner ℂ ((a q : ℂ) • f q) (f q)).re
  have hp : 0 ≤ RCLike.re
      (inner ℂ ((RCLike.ofReal (a q) : ℂ) • f q) (f q)) := by
    rw [inner_smul_real_left, RCLike.smul_re, inner_self_eq_norm_sq]
    exact mul_nonneg (ha0 q) (sq_nonneg ‖f q‖)
  simpa only [RCLike.re_to_complex, RCLike.ofReal_eq_complex_ofReal] using hp

end Multiplication

def hilbertCoordinate : C(HausdorffInterval, ℝ) where
  toFun q := (q : ℝ)
  continuous_toFun := continuous_subtype_val

def hilbertCoordinateComplement : C(HausdorffInterval, ℝ) where
  toFun q := 1 - (q : ℝ)
  continuous_toFun := continuous_const.sub continuous_subtype_val

theorem hilbertCoordinate_bound (q : HausdorffInterval) :
    |hilbertCoordinate q| ≤ 1 := by
  change |(q : ℝ)| ≤ 1
  rw [abs_of_nonneg q.property.1]
  exact q.property.2

theorem hilbertCoordinateComplement_bound (q : HausdorffInterval) :
    |hilbertCoordinateComplement q| ≤ 1 := by
  change |1 - (q : ℝ)| ≤ 1
  rw [abs_of_nonneg (sub_nonneg.mpr q.property.2)]
  linarith [q.property.1]

def coordinateOperator (σ : Measure HausdorffInterval) :
    HausdorffL2 σ →L[ℂ] HausdorffL2 σ :=
  realMultiplier σ hilbertCoordinate hilbertCoordinate_bound

theorem coordinateOperator_ae (σ : Measure HausdorffInterval) (f : HausdorffL2 σ) :
    coordinateOperator σ f =ᵐ[σ] fun q => ((q : ℝ) : ℂ) * f q :=
  realMultiplier_ae σ hilbertCoordinate hilbertCoordinate_bound f

theorem coordinateOperator_positive (σ : Measure HausdorffInterval) :
    (coordinateOperator σ).IsPositive :=
  realMultiplier_positive σ hilbertCoordinate hilbertCoordinate_bound fun q => q.property.1

theorem coordinateOperator_one_sub (σ : Measure HausdorffInterval) :
    realMultiplier σ hilbertCoordinateComplement hilbertCoordinateComplement_bound =
      1 - coordinateOperator σ := by
  apply ContinuousLinearMap.ext
  intro f
  change realMultiplier σ hilbertCoordinateComplement hilbertCoordinateComplement_bound f =
    f - coordinateOperator σ f
  apply Lp.ext
  filter_upwards [realMultiplier_ae σ hilbertCoordinateComplement
    hilbertCoordinateComplement_bound f,
    coordinateOperator_ae σ f,
    Lp.coeFn_sub f (coordinateOperator σ f)] with q hcomp hcoord hsub
  simp only [Pi.sub_apply] at hsub
  rw [hcomp, hsub, hcoord]
  change ((1 - (q : ℝ) : ℝ) : ℂ) * f q =
    f q - ((q : ℝ) : ℂ) * f q
  push_cast
  ring

theorem coordinateOperator_complement_positive (σ : Measure HausdorffInterval) :
    (1 - coordinateOperator σ).IsPositive := by
  rw [← coordinateOperator_one_sub σ]
  exact realMultiplier_positive σ hilbertCoordinateComplement
    hilbertCoordinateComplement_bound fun q => sub_nonneg.mpr q.property.2

def complexIntervalMonomial (n : ℕ) : C(HausdorffInterval, ℂ) where
  toFun q := Complex.ofReal ((q : ℝ) ^ n)
  continuous_toFun := by
    have hpow : Continuous (fun q : HausdorffInterval => (q : ℝ) ^ n) := by
      simpa only [Pi.pow_def] using
        (continuous_subtype_val : Continuous (fun q : HausdorffInterval => (q : ℝ))).pow n
    simpa only [Function.comp_def] using
      Complex.continuous_ofReal.comp hpow

def monomialVector (σ : Measure HausdorffInterval) [IsFiniteMeasure σ] (n : ℕ) :
    HausdorffL2 σ :=
  ContinuousMap.toLp 2 σ ℂ (complexIntervalMonomial n)

def unitVector (σ : Measure HausdorffInterval) [IsFiniteMeasure σ] : HausdorffL2 σ :=
  monomialVector σ 0

theorem monomialVector_ae (σ : Measure HausdorffInterval) [IsFiniteMeasure σ] (n : ℕ) :
    monomialVector σ n =ᵐ[σ] fun q => Complex.ofReal ((q : ℝ) ^ n) := by
  simpa only [monomialVector, complexIntervalMonomial, ContinuousMap.coe_mk] using
    (ContinuousMap.coeFn_toLp (E := ℂ) (p := 2) (𝕜 := ℂ)
      σ (complexIntervalMonomial n))

theorem coordinateOperator_monomial (σ : Measure HausdorffInterval)
    [IsFiniteMeasure σ] (n : ℕ) :
    coordinateOperator σ (monomialVector σ n) = monomialVector σ (n + 1) := by
  apply Lp.ext
  filter_upwards [coordinateOperator_ae σ (monomialVector σ n),
    monomialVector_ae σ n, monomialVector_ae σ (n + 1)]
    with q hmul hn hsucc
  rw [hmul, hn, hsucc]
  change Complex.ofReal (q : ℝ) * Complex.ofReal ((q : ℝ) ^ n) =
    Complex.ofReal ((q : ℝ) ^ (n + 1))
  rw [← Complex.ofReal_mul]
  apply congrArg Complex.ofReal
  rw [pow_succ]
  exact mul_comm (q : ℝ) ((q : ℝ) ^ n)

theorem coordinateOperator_pow_unitVector (σ : Measure HausdorffInterval)
    [IsFiniteMeasure σ] (n : ℕ) :
    ((coordinateOperator σ) ^ n) (unitVector σ) = monomialVector σ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ', ContinuousLinearMap.mul_apply, ih]
      exact coordinateOperator_monomial σ n

theorem unitVector_moment (σ : Measure HausdorffInterval)
    [IsFiniteMeasure σ] (n : ℕ) :
    inner ℂ (unitVector σ) (((coordinateOperator σ) ^ n) (unitVector σ)) =
      Complex.ofReal (∫ q : HausdorffInterval, ((q : ℝ) ^ n : ℝ) ∂σ) := by
  rw [coordinateOperator_pow_unitVector]
  unfold unitVector monomialVector
  rw [ContinuousMap.inner_toLp]
  simpa only [complexIntervalMonomial, ContinuousMap.coe_mk, pow_zero,
    Complex.ofReal_one, map_one, mul_one] using
    (integral_complex_ofReal (μ := σ) (f := fun q : HausdorffInterval => (q : ℝ) ^ n))

theorem unitVector_norm (σ : Measure HausdorffInterval) [IsProbabilityMeasure σ] :
    ‖unitVector σ‖ = 1 := by
  have hself : inner ℂ (unitVector σ) (unitVector σ) = 1 := by
    simpa using unitVector_moment σ 0
  have hsq : ‖unitVector σ‖ ^ 2 = 1 := by
    simpa only [RCLike.re_to_complex, hself, Complex.one_re] using
      (inner_self_eq_norm_sq (𝕜 := ℂ) (unitVector σ)).symm
  nlinarith [norm_nonneg (unitVector σ)]

/-- No realization is supplied as a premise: the L2 witness is constructed. -/
theorem hilbertRep_of_probability_moments (σ : Measure HausdorffInterval)
    [IsProbabilityMeasure σ]
    (hmom : ∀ n : ℕ, (∫ q, (q : ℝ) ^ n ∂σ) = actualNormalizedMoment n) :
    HilbertRep := by
  refine ⟨HausdorffL2 σ, inferInstance, inferInstance, inferInstance,
    coordinateOperator σ, unitVector σ,
    (coordinateOperator_positive σ).isSelfAdjoint,
    coordinateOperator_positive σ, coordinateOperator_complement_positive σ,
    unitVector_norm σ, ?_⟩
  intro n
  exact (unitVector_moment σ n).trans (congrArg Complex.ofReal (hmom n))

/-- Frozen C2 forward endpoint. The only hypothesis is native RH. -/
theorem hilbertRep_of_nativeRH (hRH : _root_.RiemannHypothesis) : HilbertRep := by
  exact hilbertRep_of_probability_moments
    (actualHausdorffMeasure (H00_of_nativeRH hRH))
    (actualHausdorffMeasure_moment (H00_of_nativeRH hRH))

end HXYThreeSpaces
