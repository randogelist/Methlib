import SingularClosure.CriticalSobolevAnalytic
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-! Regularized analytic dual functions for the L2/L6 interpolation step.
The regularization is norm(u)+δ, so its cubic integral is polynomial in δ. -/

set_option autoImplicit false
set_option Elab.async true

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SingularClosure

noncomputable section

theorem critical_continuous_memLp_cube {E : Type*} [NormedAddCommGroup E]
    (f : Vec → E) (hf : Continuous f) (p : ℝ≥0∞) :
    MemLp f p (volume.restrict unitCube) := by
  haveI : IsFiniteMeasure (volume.restrict unitCube) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using
      isCompact_unitCube.measure_lt_top (μ := volume)⟩
  obtain ⟨C, hC⟩ := isCompact_unitCube.exists_bound_of_continuousOn hf.continuousOn
  apply MemLp.of_bound hf.aestronglyMeasurable C
  filter_upwards [ae_restrict_mem isCompact_unitCube.measurableSet] with x hx
  exact hC x hx

theorem critical_cube_pairing_bound (f g : Vec → ℂ)
    (hf : Continuous f) (hg : Continuous g) {p q : ℝ}
    (hpq : p.HolderConjugate q) :
    ‖∫ x in unitCube, f x * g x‖ ≤
      lpNorm f (ENNReal.ofReal p) (volume.restrict unitCube) *
        lpNorm g (ENNReal.ofReal q) (volume.restrict unitCube) := by
  have h := integral_mul_norm_le_Lp_mul_Lq hpq
    (critical_continuous_memLp_cube f hf (ENNReal.ofReal p))
    (critical_continuous_memLp_cube g hg (ENNReal.ofReal q))
  calc
    _ ≤ ∫ x in unitCube, ‖f x * g x‖ := norm_integral_le_integral_norm _
    _ = ∫ x in unitCube, ‖f x‖ * ‖g x‖ := by simp only [norm_mul]
    _ ≤ _ := by
      simpa only [lpNorm_eq_integral_norm_rpow_toReal
        (ENNReal.ofReal_ne_zero_iff.mpr hpq.pos) ENNReal.ofReal_ne_top
          hf.aestronglyMeasurable,
        lpNorm_eq_integral_norm_rpow_toReal
        (ENNReal.ofReal_ne_zero_iff.mpr hpq.symm.pos) ENNReal.ofReal_ne_top
          hg.aestronglyMeasurable,
        ENNReal.toReal_ofReal hpq.nonneg, ENNReal.toReal_ofReal hpq.symm.nonneg,
        one_div] using h

def criticalDualBase (u : Vec → ℂ) (δ : ℝ) (x : Vec) : ℝ := ‖u x‖ + δ

def criticalDualMass (u : Vec → ℂ) (δ : ℝ) : ℝ :=
  ∫ x in unitCube, criticalDualBase u δ x ^ 3

def criticalDualFamily (u : Vec → ℂ) (δ : ℝ) (z : ℂ) (x : Vec) : ℂ :=
  star (u x) * criticalComplexWeight (criticalDualBase u δ x) (z + 1 / 2)

theorem criticalDualBase_pos (u : Vec → ℂ) {δ : ℝ} (hδ : 0 < δ) (x : Vec) :
    0 < criticalDualBase u δ x := add_pos_of_nonneg_of_pos (norm_nonneg _) hδ

theorem criticalDualBase_continuous (u : Vec → ℂ) (hu : Continuous u) (δ : ℝ) :
    Continuous (criticalDualBase u δ) := hu.norm.add_const δ

theorem criticalDualMass_nonneg (u : Vec → ℂ) {δ : ℝ} (hδ : 0 ≤ δ) :
    0 ≤ criticalDualMass u δ := by
  apply integral_nonneg
  intro x
  exact pow_nonneg (add_nonneg (norm_nonneg _) hδ) 3

theorem criticalDualFamily_continuous (u : Vec → ℂ) (hu : Continuous u)
    {δ : ℝ} (hδ : 0 < δ) :
    Continuous (fun q : ℂ × Vec => criticalDualFamily u δ q.1 q.2) := by
  have hlog : Continuous (fun x => Real.log (criticalDualBase u δ x)) :=
    (criticalDualBase_continuous u hu δ).log
      (fun x => (criticalDualBase_pos u hδ x).ne')
  unfold criticalDualFamily criticalComplexWeight
  exact (hu.comp continuous_snd).star.mul
    (Complex.continuous_exp.comp ((continuous_fst.add continuous_const).mul
      (Complex.continuous_ofReal.comp (hlog.comp continuous_snd))))

theorem criticalDualFamily_hasDerivAt (u : Vec → ℂ) (δ : ℝ) (z : ℂ) (x : Vec) :
    HasDerivAt (fun w => criticalDualFamily u δ w x)
      (criticalDualFamily u δ z x * (Real.log (criticalDualBase u δ x) : ℂ)) z := by
  have h := (criticalComplexWeight_hasDerivAt (criticalDualBase u δ x) (z + 1 / 2)).comp z
    ((hasDerivAt_id z).add_const (1 / 2 : ℂ))
  have h' := h.const_mul (star (u x))
  simpa only [criticalDualFamily, mul_one, mul_assoc] using! h'

theorem criticalDualFamily_norm (u : Vec → ℂ) {δ : ℝ} (hδ : 0 < δ)
    (z : ℂ) (x : Vec) :
    ‖criticalDualFamily u δ z x‖ =
      ‖u x‖ * criticalDualBase u δ x ^ (z.re + 1 / 2) := by
  rw [criticalDualFamily, norm_mul, norm_star,
    criticalComplexWeight_norm (criticalDualBase_pos u hδ x)]
  simp only [Complex.add_re, Complex.div_ofNat_re, Complex.one_re]

theorem criticalComplexWeight_one {w : ℝ} (hw : 0 < w) :
    criticalComplexWeight w 1 = (w : ℂ) := by
  simp only [criticalComplexWeight, one_mul, ← Complex.ofReal_exp, Real.exp_log hw]

theorem criticalDualFamily_midpoint (u : Vec → ℂ) {δ : ℝ} (hδ : 0 < δ) (x : Vec) :
    criticalDualFamily u δ (1 / 2) x =
      star (u x) * (criticalDualBase u δ x : ℂ) := by
  unfold criticalDualFamily
  rw [show (1 / 2 : ℂ) + 1 / 2 = 1 by norm_num,
    criticalComplexWeight_one (criticalDualBase_pos u hδ x)]

/-- The endpoint dual powers are bounded by one common cubic majorant. -/
theorem criticalDualFamily_norm_rpow_le (u : Vec → ℂ) {δ : ℝ} (hδ : 0 < δ)
    (z : ℂ) (p : ℝ) (hp : 0 ≤ p) (hpower : (z.re + 3 / 2) * p = 3) (x : Vec) :
    ‖criticalDualFamily u δ z x‖ ^ p ≤ criticalDualBase u δ x ^ 3 := by
  have hq := criticalDualBase_pos u hδ x
  have hnorm : ‖criticalDualFamily u δ z x‖ ≤
      criticalDualBase u δ x ^ (z.re + 3 / 2) := by
    rw [criticalDualFamily_norm u hδ]
    calc
      _ ≤ criticalDualBase u δ x * criticalDualBase u δ x ^ (z.re + 1 / 2) :=
        mul_le_mul_of_nonneg_right (by dsimp [criticalDualBase]; linarith)
          (Real.rpow_nonneg hq.le _)
      _ = criticalDualBase u δ x ^ (1 + (z.re + 1 / 2)) := by
        rw [Real.rpow_add hq, Real.rpow_one]
      _ = _ := by congr 1; ring
  calc
    _ ≤ (criticalDualBase u δ x ^ (z.re + 3 / 2)) ^ p :=
      Real.rpow_le_rpow (norm_nonneg _) hnorm hp
    _ = _ := by
      rw [← Real.rpow_mul hq.le, hpower, Real.rpow_ofNat]

theorem criticalDualFamily_lpNorm_le (u : Vec → ℂ) (hu : Continuous u)
    {δ : ℝ} (hδ : 0 < δ) (z : ℂ) (p : ℝ) (hp : 0 < p)
    (hpower : (z.re + 3 / 2) * p = 3) :
    lpNorm (criticalDualFamily u δ z) (ENNReal.ofReal p) (volume.restrict unitCube) ≤
      criticalDualMass u δ ^ (1 / p) := by
  have hg : Continuous (criticalDualFamily u δ z) :=
    (criticalDualFamily_continuous u hu hδ).comp (continuous_const.prodMk continuous_id)
  rw [lpNorm_eq_integral_norm_rpow_toReal
    (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top hg.aestronglyMeasurable,
    ENNReal.toReal_ofReal hp.le]
  apply Real.rpow_le_rpow
    (integral_nonneg (fun x => Real.rpow_nonneg (norm_nonneg _) _)) _ (by positivity)
  exact integral_mono
    ((hg.norm.rpow_const (fun _ => Or.inr hp.le)).continuousOn.integrableOn_compact
      isCompact_unitCube)
    (((criticalDualBase_continuous u hu δ).pow 3).continuousOn.integrableOn_compact
      isCompact_unitCube)
    (criticalDualFamily_norm_rpow_le u hδ z p hp.le hpower)

end

end SingularClosure
