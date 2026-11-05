import PeriodicShearProfile
import PeriodicShearGrowth
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

noncomputable section

namespace CondFeffB

open Set
open scoped ContDiff

private def wave (k : ℕ) : ℝ := 2 * Real.pi * ((k + 1 : ℕ) : ℝ)
private def decay (ν : ℝ) (k : ℕ) : ℝ := -(4 * Real.pi ^ 2 * ν * ((k + 1 : ℕ) : ℝ) ^ 2)
private def weight (k : ℕ) : ℝ := Real.exp (-((k + 1 : ℕ) : ℝ))
private def coeff (ν t : ℝ) (k : ℕ) : ℝ := weight k * Real.exp (decay ν k * t)

private def slopeMode (ν t y : ℝ) (k : ℕ) : ℝ :=
  (-wave k * coeff ν t k) * Real.sin (wave k * y)

private def curvatureMode (ν t y : ℝ) (k : ℕ) : ℝ :=
  (-(wave k ^ 2) * coeff ν t k) * Real.cos (wave k * y)

def shearSlope (ν t y : ℝ) : ℝ := ∑' k : ℕ, slopeMode ν t y k

def shearCurvature (ν t y : ℝ) : ℝ := ∑' k : ℕ, curvatureMode ν t y k

private def envelope (d k : ℕ) : ℝ :=
  (2 * Real.pi) ^ d * PeriodicShear.weightedPower d (k+1)

private theorem envelope_summable (d : ℕ) : Summable (envelope d) :=
  (PeriodicShear.summable_weightedPower_succ d).mul_left ((2 * Real.pi) ^ d)

private theorem coeff_nonneg (ν t : ℝ) (k : ℕ) : 0 ≤ coeff ν t k := by
  unfold coeff weight
  positivity

private theorem wave_nonneg (k : ℕ) : 0 ≤ wave k := by unfold wave; positivity

private theorem coeff_le_weight {ν t : ℝ} (hν : 0 ≤ ν) (ht : 0 ≤ t) (k : ℕ) :
    coeff ν t k ≤ weight k := by
  have hd : decay ν k ≤ 0 := by
    unfold decay
    exact neg_nonpos.mpr (by positivity)
  have he : Real.exp (decay ν k * t) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg hd ht)
  have hw : 0 ≤ weight k := by
    unfold weight
    exact (Real.exp_pos _).le
  change weight k * Real.exp (decay ν k * t) ≤ weight k
  exact mul_le_of_le_one_right hw he

private theorem slopeMode_bound {ν t : ℝ} (hν : 0 ≤ ν) (ht : 0 ≤ t) (y : ℝ) (k : ℕ) :
    ‖slopeMode ν t y k‖ ≤ envelope 1 k := by
  rw [slopeMode, Real.norm_eq_abs, abs_mul, abs_mul, abs_neg,
    abs_of_nonneg (wave_nonneg k), abs_of_nonneg (coeff_nonneg _ _ _)]
  calc
    _ ≤ wave k * coeff ν t k := mul_le_of_le_one_right
      (mul_nonneg (wave_nonneg k) (coeff_nonneg _ _ _)) (Real.abs_sin_le_one _)
    _ ≤ wave k * weight k := mul_le_mul_of_nonneg_left (coeff_le_weight hν ht k) (wave_nonneg k)
    _ = envelope 1 k := by simp only [wave, weight, envelope, PeriodicShear.weightedPower, pow_one]; ring

private theorem curvatureMode_bound {ν t : ℝ} (hν : 0 ≤ ν) (ht : 0 ≤ t) (y : ℝ) (k : ℕ) :
    ‖curvatureMode ν t y k‖ ≤ envelope 2 k := by
  rw [curvatureMode, Real.norm_eq_abs, abs_mul, abs_mul, abs_neg,
    abs_of_nonneg (sq_nonneg _), abs_of_nonneg (coeff_nonneg _ _ _)]
  calc
    _ ≤ wave k ^ 2 * coeff ν t k := mul_le_of_le_one_right
      (mul_nonneg (sq_nonneg _) (coeff_nonneg _ _ _)) (Real.abs_cos_le_one _)
    _ ≤ wave k ^ 2 * weight k := mul_le_mul_of_nonneg_left (coeff_le_weight hν ht k) (sq_nonneg _)
    _ = envelope 2 k := by unfold wave weight envelope PeriodicShear.weightedPower; ring

private theorem slopeMode_hasDerivAt (ν t y : ℝ) (k : ℕ) :
    HasDerivAt (fun s => shearMode ν t s k) (slopeMode ν t y k) y := by
  have h := ((hasDerivAt_const_mul (x := y) (wave k)).cos).const_mul (coeff ν t k)
  have hs : slopeMode ν t y k =
      coeff ν t k * (-Real.sin (wave k * y) * wave k) := by
    unfold slopeMode
    ring
  rw [hs]
  exact h

private theorem curvatureMode_hasDerivAt (ν t y : ℝ) (k : ℕ) :
    HasDerivAt (fun s => slopeMode ν t s k) (curvatureMode ν t y k) y := by
  have h := ((hasDerivAt_const_mul (x := y) (wave k)).sin).const_mul (-wave k * coeff ν t k)
  have hc : curvatureMode ν t y k =
      (-wave k * coeff ν t k) * (Real.cos (wave k * y) * wave k) := by
    unfold curvatureMode
    ring
  rw [hc]
  exact h

private theorem timeMode_hasDerivAt (ν t y : ℝ) (k : ℕ) :
    HasDerivAt (fun s => shearMode ν s y k) (ν * curvatureMode ν t y k) t := by
  have h := (((hasDerivAt_const_mul (x := t) (decay ν k)).exp).const_mul
    (weight k)).mul_const (Real.cos (wave k * y))
  have hd : decay ν k = -ν * (wave k) ^ 2 := by
    unfold decay wave
    ring
  have ht : ν * curvatureMode ν t y k =
      (weight k * (Real.exp (decay ν k * t) * decay ν k)) * Real.cos (wave k * y) := by
    unfold curvatureMode coeff
    rw [hd]
    ring
  rw [ht]
  exact h

theorem shearProfile_hasDerivAt_space {ν t : ℝ} (hν : 0 ≤ ν) (ht : 0 ≤ t) (y : ℝ) :
    HasDerivAt (shearProfile ν t) (shearSlope ν t y) y := by
  exact hasDerivAt_tsum (g := fun k s => shearMode ν t s k)
    (g' := fun k s => slopeMode ν t s k) (y₀ := 0)
    (envelope_summable 1) (fun k s => slopeMode_hasDerivAt ν t s k)
    (fun k s => slopeMode_bound hν ht s k) (shearMode_summable ν t 0 hν ht) y

theorem shearSlope_hasDerivAt_space {ν t : ℝ} (hν : 0 ≤ ν) (ht : 0 ≤ t) (y : ℝ) :
    HasDerivAt (shearSlope ν t) (shearCurvature ν t y) y := by
  exact hasDerivAt_tsum (g := fun k s => slopeMode ν t s k)
    (g' := fun k s => curvatureMode ν t s k) (y₀ := 0)
    (envelope_summable 2) (fun k s => curvatureMode_hasDerivAt ν t s k)
    (fun k s => curvatureMode_bound hν ht s k)
    ((envelope_summable 1).of_norm_bounded (fun k => slopeMode_bound hν ht 0 k)) y

/-- The positive-time PDE on the scalar shear, with its Laplacian given by its
second classical spatial derivative. -/
theorem shearProfile_hasDerivAt_time {ν t : ℝ} (hν : 0 ≤ ν) (ht : 0 < t) (y : ℝ) :
    HasDerivAt (fun s => shearProfile ν s y) (ν * shearCurvature ν t y) t := by
  have h := hasDerivAt_tsum_of_isPreconnected
    (g := fun k s => shearMode ν s y k) (g' := fun k s => ν * curvatureMode ν s y k)
    (t := Ioi (0 : ℝ)) (y₀ := 1) ((envelope_summable 2).mul_left ν)
    isOpen_Ioi isPreconnected_Ioi (fun k s _ => timeMode_hasDerivAt ν s y k)
    (fun k s hs => show ‖ν * curvatureMode ν s y k‖ ≤ ν * envelope 2 k from by
      rw [norm_mul, Real.norm_eq_abs ν, abs_of_nonneg hν]
      exact mul_le_mul_of_nonneg_left (curvatureMode_bound hν (le_of_lt hs) y k) hν)
    (by norm_num) (shearMode_summable ν 1 y hν (by norm_num)) ht
  simpa only [shearProfile, shearCurvature, tsum_mul_left] using h

/-- Uniform bound used in the classical periodic velocity-difference estimate. -/
def shearSlopeBound : ℝ := ∑' k : ℕ, envelope 1 k

theorem shearSlopeBound_nonneg : 0 ≤ shearSlopeBound := by
  apply tsum_nonneg
  intro k
  exact mul_nonneg (by positivity) (PeriodicShear.weightedPower_nonneg 1 (k+1))

theorem abs_shearSlope_le {ν t : ℝ} (hν : 0 ≤ ν) (ht : 0 ≤ t) (y : ℝ) :
    |shearSlope ν t y| ≤ shearSlopeBound := by
  have hnorm : Summable (fun k : ℕ => ‖slopeMode ν t y k‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => slopeMode_bound hν ht y k)
      (envelope_summable 1)
  rw [← Real.norm_eq_abs]
  exact (norm_tsum_le_tsum_norm hnorm).trans
    (hnorm.tsum_le_tsum (fun k => slopeMode_bound hν ht y k) (envelope_summable 1))

/-- Joint continuity of both spatial derivative sums on the closed time half-space. -/
theorem shearSlope_continuousOn (ν : ℝ) (hν : 0 ≤ ν) :
    ContinuousOn (fun z : ℝ × ℝ => shearSlope ν z.1 z.2) {z | 0 ≤ z.1} := by
  exact continuousOn_tsum (f := fun k (z : ℝ × ℝ) => slopeMode ν z.1 z.2 k)
    (fun k => by unfold slopeMode coeff; fun_prop)
    (envelope_summable 1) (fun k x hx => slopeMode_bound hν hx x.2 k)

theorem shearCurvature_continuousOn (ν : ℝ) (hν : 0 ≤ ν) :
    ContinuousOn (fun z : ℝ × ℝ => shearCurvature ν z.1 z.2) {z | 0 ≤ z.1} := by
  exact continuousOn_tsum (f := fun k (z : ℝ × ℝ) => curvatureMode ν z.1 z.2 k)
    (fun k => by unfold curvatureMode coeff; fun_prop)
    (envelope_summable 2) (fun k x hx => curvatureMode_bound hν hx x.2 k)

/-- Regularity of each spatial slice needed for the flux divergence theorem. -/
theorem shearSlope_contDiff_one {ν t : ℝ} (hν : 0 ≤ ν) (ht : 0 ≤ t) :
    ContDiff ℝ 1 (shearSlope ν t) := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun y => (shearSlope_hasDerivAt_space hν ht y).differentiableAt, ?_⟩
  rw [show deriv (shearSlope ν t) = shearCurvature ν t from
    funext (fun y => (shearSlope_hasDerivAt_space hν ht y).deriv)]
  exact (shearCurvature_continuousOn ν hν).comp_continuous (f := fun y : ℝ => (t, y))
    (continuous_const.prodMk continuous_id) (fun _ => ht)

theorem shearProfile_contDiff_two {ν t : ℝ} (hν : 0 ≤ ν) (ht : 0 ≤ t) :
    ContDiff ℝ 2 (shearProfile ν t) := by
  change ContDiff ℝ ((1 : ℕ∞ω) + 1) (shearProfile ν t)
  apply contDiff_succ_iff_deriv.mpr
  refine ⟨fun y => (shearProfile_hasDerivAt_space hν ht y).differentiableAt, ?_, ?_⟩
  · simp
  · rw [show deriv (shearProfile ν t) = shearSlope ν t from
      funext (fun y => (shearProfile_hasDerivAt_space hν ht y).deriv)]
    exact shearSlope_contDiff_one hν ht

end CondFeffB
