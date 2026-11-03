import HVR_Prime_Summability
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Ring

noncomputable section

/-!
Real higher-prime-power correction in its geometrically resummed form.
This module does not assert a complex analytic continuation, exchange of
both sums, any identity with zeta, or the prime number theorem.
-/
namespace HVRPrimePowerCorrection

open HVRPrimeSummability

def ratio (sigma : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-sigma * Real.log (n : ℝ))

def correctionTerm (sigma : ℝ) (n : ℕ) : ℝ :=
  if Nat.Prime n then primeWeightSeries (2 * sigma) n / (1 - ratio sigma n) else 0

theorem denominator_uniform_pos (sigma : ℝ) (hsigma : (1 / 2 : ℝ) < sigma) :
    0 < 1 - ratio sigma 2 := by
  have hs : 0 < sigma := by linarith
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have harg : -sigma * Real.log (2 : ℝ) < 0 := by
    have hmul : 0 < sigma * Real.log (2 : ℝ) := mul_pos hs hlog
    linarith
  have hratio : ratio sigma 2 < 1 := by
    dsimp [ratio]
    exact Real.exp_lt_one_iff.mpr harg
  linarith

theorem ratio_le_two (sigma : ℝ) (hsigma : (1 / 2 : ℝ) < sigma)
    {p : ℕ} (hp : Nat.Prime p) :
    ratio sigma p ≤ ratio sigma 2 := by
  have hs : 0 ≤ sigma := by linarith
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hlog : Real.log (2 : ℝ) ≤ Real.log (p : ℝ) :=
    Real.log_le_log (by norm_num) hp2
  have hprod := mul_nonneg hs (sub_nonneg.mpr hlog)
  dsimp [ratio]
  apply Real.exp_le_exp.mpr
  nlinarith

theorem correctionTerm_nonneg (sigma : ℝ) (hsigma : (1 / 2 : ℝ) < sigma)
    (n : ℕ) : 0 ≤ correctionTerm sigma n := by
  by_cases hp : Nat.Prime n
  · have hlower : 0 < 1 - ratio sigma 2 := denominator_uniform_pos sigma hsigma
    have hratio : ratio sigma n ≤ ratio sigma 2 := ratio_le_two sigma hsigma hp
    have hden : 0 ≤ 1 - ratio sigma n := by linarith
    simp only [correctionTerm, hp, if_true]
    exact div_nonneg (primeWeightSeries_nonneg (2 * sigma) n) hden
  · simp [correctionTerm, hp]

theorem correctionTerm_le (sigma : ℝ) (hsigma : (1 / 2 : ℝ) < sigma)
    (n : ℕ) :
    correctionTerm sigma n ≤ primeWeightSeries (2 * sigma) n / (1 - ratio sigma 2) := by
  by_cases hp : Nat.Prime n
  · have hlower : 0 < 1 - ratio sigma 2 := denominator_uniform_pos sigma hsigma
    have hratio : ratio sigma n ≤ ratio sigma 2 := ratio_le_two sigma hsigma hp
    have hden : 1 - ratio sigma 2 ≤ 1 - ratio sigma n := by linarith
    simp only [correctionTerm, hp, if_true]
    exact div_le_div_of_nonneg_left (primeWeightSeries_nonneg (2 * sigma) n) hlower hden
  · simp only [correctionTerm, hp, if_false]
    exact div_nonneg (primeWeightSeries_nonneg (2 * sigma) n)
      (le_of_lt (denominator_uniform_pos sigma hsigma))

/-- The resummed real correction is absolutely summable for sigma > 1/2. -/
theorem correction_summable (sigma : ℝ) (hsigma : (1 / 2 : ℝ) < sigma) :
    Summable (correctionTerm sigma) := by
  have htwo : 1 < 2 * sigma := by linarith
  have hweight := primeWeightSeries_summable (2 * sigma) htwo
  have hmajorant : Summable (fun n : ℕ =>
      primeWeightSeries (2 * sigma) n / (1 - ratio sigma 2)) :=
    hweight.div_const (1 - ratio sigma 2)
  exact Summable.of_nonneg_of_le (correctionTerm_nonneg sigma hsigma)
    (correctionTerm_le sigma hsigma) hmajorant

/-- Nonnegativity makes the real correction absolutely summable. -/
theorem correction_abs_summable (sigma : ℝ) (hsigma : (1 / 2 : ℝ) < sigma) :
    Summable (fun n => |correctionTerm sigma n|) := by
  have habs : (fun n => |correctionTerm sigma n|) = correctionTerm sigma := by
    funext n
    exact abs_of_nonneg (correctionTerm_nonneg sigma hsigma n)
  rw [habs]
  exact correction_summable sigma hsigma

/-- For each prime, the closed correction is the sum of its geometric tail.
The kth summand is the weight at twice sigma times the kth power of the
prime ratio. The exchange of the prime and exponent sums is not claimed. -/
theorem correction_geometric_hasSum (sigma : ℝ) (hsigma : (1 / 2 : ℝ) < sigma)
    {p : ℕ} (hp : Nat.Prime p) :
    HasSum (fun k : ℕ => primeWeightSeries (2 * sigma) p * (ratio sigma p) ^ k)
      (correctionTerm sigma p) := by
  have hrnonneg : 0 ≤ ratio sigma p := by
    dsimp [ratio]
    exact le_of_lt (Real.exp_pos _)
  have hrlt : ratio sigma p < 1 := by
    have hle := ratio_le_two sigma hsigma hp
    have hpos := denominator_uniform_pos sigma hsigma
    linarith
  have hgeom := hasSum_geometric_of_lt_one hrnonneg hrlt
  have hscaled := hgeom.mul_left (primeWeightSeries (2 * sigma) p)
  simpa only [correctionTerm, hp, if_true, div_eq_mul_inv] using hscaled

end HVRPrimePowerCorrection
