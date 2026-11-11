import SingularClosure.CriticalSmoothEnergy
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! Positive-time continuity of the actual physical L6 norm, derived from
joint smoothness and dominated integration on compact positive-time slabs. -/

set_option autoImplicit false
set_option Elab.async true

open Set Filter MeasureTheory
open scoped ContDiff ENNReal Topology

namespace SingularClosure

noncomputable section

theorem critical_eLpNorm_six_toReal_eq_rpow_integral
    (v : Field) (hv : Continuous v) :
    (eLpNorm v 6 (volume.restrict unitCube)).toReal =
      (∫ x in unitCube, ‖v x‖ ^ 6) ^ (1 / 6 : ℝ) := by
  have hm : AEStronglyMeasurable v (volume.restrict unitCube) := hv.aestronglyMeasurable
  have h := (toReal_eLpNorm (p := 6) hm).trans
    (lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num) hm)
  simpa only [ENNReal.toReal_ofNat, Real.rpow_ofNat, one_div] using h

/-- At every positive time, the genuine cube L6 norm is continuous. -/
theorem CriticalPositiveSolenoidalTest.eLpNorm_six_toReal_continuousAt
    {u : Velocity} (hu : CriticalPositiveSolenoidalTest u)
    (t : ℝ) (ht : 0 < t) :
    ContinuousAt (fun r => (eLpNorm (u r) 6 (volume.restrict unitCube)).toReal) t := by
  have hJ : ContinuousAt (fun r => ∫ x in unitCube, ‖u r x‖ ^ 6) t :=
    (critical_real_cube_integral_continuousOn_Icc
      (fun r x => ‖u r x‖ ^ 6) (hu.smooth.continuousOn.norm.pow 6)
      (t / 2) (t + 1) (by linarith)).continuousAt
      (Icc_mem_nhds (by linarith) (by linarith))
  have hp : ContinuousAt
      (fun r => (∫ x in unitCube, ‖u r x‖ ^ 6) ^ (1 / 6 : ℝ)) t :=
    (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 1 / 6)).continuousAt.comp t hJ
  apply hp.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ht] with r hr
  exact critical_eLpNorm_six_toReal_eq_rpow_integral (u r) (hu.spatial_smooth hr).continuous

/-- No regularity at zero is needed for continuity on `(0,T]`. -/
theorem CriticalPositiveSolenoidalTest.eLpNorm_six_toReal_continuousOn
    {u : Velocity} (hu : CriticalPositiveSolenoidalTest u) (T : ℝ) :
    ContinuousOn (fun r => (eLpNorm (u r) 6 (volume.restrict unitCube)).toReal)
      (Ioc (0 : ℝ) T) := by
  intro t ht
  exact (hu.eLpNorm_six_toReal_continuousAt t ht.1).continuousWithinAt

end

end SingularClosure
