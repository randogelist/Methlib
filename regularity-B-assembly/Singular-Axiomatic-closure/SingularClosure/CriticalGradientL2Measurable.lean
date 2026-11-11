import SingularClosure.CriticalPositiveFlow
import SingularClosure.CriticalLerayHopf
import SingularClosure.CriticalSmoothEnergy
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! The actual spatial gradient is a measurable physical L2-valued time path.

The proof uses local positive-time joint smoothness and dominated cube
integration. It applies to the operator norm on spatial derivatives, without
identifying that norm with the Hilbert--Schmidt norm.
-/

set_option autoImplicit false
set_option Elab.async true

open Set Filter MeasureTheory
open scoped ContDiff ENNReal Topology

namespace SingularClosure

noncomputable section

theorem criticalL2Representative_dist_eq_integral_rpow
    {E : Type*} [NormedAddCommGroup E]
    (f g : Vec → E) (hf : MemLp f 2 (volume.restrict unitCube))
    (hg : MemLp g 2 (volume.restrict unitCube)) :
    dist (criticalL2Representative f) (criticalL2Representative g) =
      (∫ x in unitCube, ‖f x - g x‖ ^ 2) ^ (1 / 2 : ℝ) := by
  rw [criticalL2Representative_eq f hf, criticalL2Representative_eq g hg,
    dist_eq_norm, ← hf.toLp_sub hg, Lp.norm_toLp]
  have h := (toReal_eLpNorm (p := (2 : ℝ≥0∞)) (hf.sub hg).aestronglyMeasurable).trans
    (lpNorm_eq_integral_norm_rpow_toReal (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num)
      (hf.sub hg).aestronglyMeasurable)
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, one_div, Pi.sub_apply] using h

/-- A jointly continuous positive-time field has a continuous actual cube L2 path. -/
theorem criticalL2Representative_continuousAt_of_joint
    {E : Type*} [NormedAddCommGroup E]
    (F : ℝ → Vec → E)
    (hF : ContinuousOn (fun z : ℝ × Vec => F z.1 z.2) {z | 0 < z.1})
    (t : ℝ) (ht : 0 < t) :
    ContinuousAt (fun r => criticalL2Representative (F r)) t := by
  have hFc (r : ℝ) (hr : 0 < r) : Continuous (F r) :=
    hF.comp_continuous (continuous_const.prodMk continuous_id) (fun _ => hr)
  have hmem (r : ℝ) (hr : 0 < r) : MemLp (F r) 2 (volume.restrict unitCube) :=
    critical_continuous_memLp_cube (F r) (hFc r hr) 2
  have hdiff : ContinuousOn
      (fun z : ℝ × Vec => F z.1 z.2 - F t z.2) {z | 0 < z.1} :=
    hF.sub ((hFc t ht).comp continuous_snd).continuousOn
  have hJ : ContinuousAt (fun r => ∫ x in unitCube, ‖F r x - F t x‖ ^ 2) t :=
    (critical_real_cube_integral_continuousOn_Icc
      (fun r x => ‖F r x - F t x‖ ^ 2) (hdiff.norm.pow 2)
      (t / 2) (t + 1) (by linarith)).continuousAt
        (Icc_mem_nhds (by linarith) (by linarith))
  have hp : ContinuousAt
      (fun r => (∫ x in unitCube, ‖F r x - F t x‖ ^ 2) ^ (1 / 2 : ℝ)) t :=
    (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 1 / 2)).continuousAt.comp t hJ
  have hlim : Tendsto
      (fun r => (∫ x in unitCube, ‖F r x - F t x‖ ^ 2) ^ (1 / 2 : ℝ))
      (𝓝 t) (𝓝 0) := by
    simpa only [sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
      integral_zero, Real.zero_rpow (by norm_num : (1 / 2 : ℝ) ≠ 0)] using hp.tendsto
  apply tendsto_iff_dist_tendsto_zero.mpr
  have heq : (fun r => dist (criticalL2Representative (F r))
      (criticalL2Representative (F t))) =ᶠ[𝓝 t]
      (fun r => (∫ x in unitCube, ‖F r x - F t x‖ ^ 2) ^ (1 / 2 : ℝ)) := by
    filter_upwards [Ioi_mem_nhds ht] with r hr
    exact criticalL2Representative_dist_eq_integral_rpow (F r) (F t) (hmem r hr) (hmem t ht)
  exact (tendsto_congr' heq).mpr hlim

theorem criticalPositive_spatial_fderiv_eq_joint
    {ν : ℝ} (L : CriticalPositiveSobolevFlow ν)
    (t : ℝ) (ht : 0 < t) (x : Vec) :
    fderiv ℝ (L.velocity t) x =
      (fderiv ℝ (fun z : ℝ × Vec => L.velocity z.1 z.2) (t, x)).comp
        (ContinuousLinearMap.inr ℝ ℝ Vec) := by
  have hopen : IsOpen positiveSpacetime := isOpen_lt continuous_const continuous_fst
  have hd : DifferentiableAt ℝ (fun z : ℝ × Vec => L.velocity z.1 z.2) (t, x) :=
    (L.velocity_spacetime_smooth.contDiffAt (hopen.mem_nhds ht)).differentiableAt (by simp)
  have hpath : HasFDerivAt (fun y : Vec => (t, y)) (ContinuousLinearMap.inr ℝ ℝ Vec) x :=
    hasFDerivAt_prodMk_right t x
  simpa only [Function.comp_def] using (hd.hasFDerivAt.comp x hpath).fderiv

theorem criticalPositive_spatial_fderiv_joint_continuous
    {ν : ℝ} (L : CriticalPositiveSobolevFlow ν) :
    ContinuousOn (fun z : ℝ × Vec => fderiv ℝ (L.velocity z.1) z.2) positiveSpacetime := by
  have hopen : IsOpen positiveSpacetime := isOpen_lt continuous_const continuous_fst
  have hfd := L.velocity_spacetime_smooth.continuousOn_fderiv_of_isOpen hopen (by simp)
  have hcomp : ContinuousOn
      (fun z : ℝ × Vec =>
        (fderiv ℝ (fun w : ℝ × Vec => L.velocity w.1 w.2) z).comp
          (ContinuousLinearMap.inr ℝ ℝ Vec)) positiveSpacetime :=
    hfd.clm_comp continuousOn_const
  apply hcomp.congr
  intro z hz
  exact criticalPositive_spatial_fderiv_eq_joint L z.1 hz z.2

theorem criticalPositive_gradientL2_continuousOn
    {ν : ℝ} (L : CriticalPositiveSobolevFlow ν) :
    ContinuousOn (fun t => criticalL2Representative (fderiv ℝ (L.velocity t))) (Ioi 0) := by
  intro t ht
  exact (criticalL2Representative_continuousAt_of_joint
    (fun t => fderiv ℝ (L.velocity t))
    (criticalPositive_spatial_fderiv_joint_continuous L) t ht).continuousWithinAt

/-- Actual operator-valued physical gradients form a Bochner-measurable L2 path. -/
theorem criticalPositive_gradientL2_aestronglyMeasurable
    {ν : ℝ} (L : CriticalPositiveSobolevFlow ν) (T : ℝ) :
    AEStronglyMeasurable (fun t => criticalL2Representative (fderiv ℝ (L.velocity t)))
      (volume.restrict (Ioc (0 : ℝ) T)) :=
  ((criticalPositive_gradientL2_continuousOn L).mono (fun _ ht => ht.1)).
    aestronglyMeasurable measurableSet_Ioc

end

end SingularClosure
