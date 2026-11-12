import SingularClosure.CriticalPositiveFlow
import SingularClosure.CriticalSerrinEstimate
import Mathlib.MeasureTheory.Measure.Prod

/-! Parameter measurability of the actual spatial norm of the positive
smooth flow. A measurable zero extension outside positive time is used
only to apply the actual cube lintegral measurability theorem. -/

set_option autoImplicit false
set_option Elab.async true
open Set MeasureTheory
open scoped ENNReal

namespace SingularClosure
noncomputable section

theorem criticalPositive_spatialNorm_aestronglyMeasurable
    {ν : ℝ} (L : CriticalPositiveSobolevFlow ν)
    (p : ℝ≥0∞) (hp0 : p ≠ 0) (hpTop : p ≠ ⊤) (T : ℝ) :
    AEStronglyMeasurable (fun t => criticalSpatialNorm p (L.velocity t))
      (volume.restrict (Ioc (0 : ℝ) T)) := by
  classical
  let F : ℝ × Vec → Vec :=
    positiveSpacetime.piecewise (fun z => L.velocity z.1 z.2) (fun _ => 0)
  have hpos : MeasurableSet positiveSpacetime :=
    (isOpen_lt continuous_const continuous_fst).measurableSet
  have hF : Measurable F :=
    L.velocity_spacetime_smooth.continuousOn.measurable_piecewise continuousOn_const hpos
  have hnorm : Measurable (fun t => criticalSpatialNorm p (fun x => F (t, x))) := by
    simp_rw [criticalSpatialNorm, eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpTop]
    exact (((hF.enorm.pow_const p.toReal).lintegral_prod_right').pow_const
      (1 / p.toReal)).ennreal_toReal
  apply hnorm.aestronglyMeasurable.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  apply congrArg (criticalSpatialNorm p)
  funext x
  change positiveSpacetime.piecewise (fun z => L.velocity z.1 z.2)
    (fun _ => 0) (t, x) = L.velocity t x
  exact positiveSpacetime.piecewise_eq_of_mem _ _
    (show (t, x) ∈ positiveSpacetime from ht.1)

theorem criticalPositive_spatialNorm_six_aestronglyMeasurable
    {ν : ℝ} (L : CriticalPositiveSobolevFlow ν) (T : ℝ) :
    AEStronglyMeasurable (fun t => criticalSpatialNorm 6 (L.velocity t))
      (volume.restrict (Ioc (0 : ℝ) T)) :=
  criticalPositive_spatialNorm_aestronglyMeasurable L 6 (by norm_num) (by norm_num) T

theorem criticalPositive_spatialNorm_aestronglyMeasurable_Ioi
    {ν : ℝ} (L : CriticalPositiveSobolevFlow ν)
    (p : ℝ≥0∞) (hp0 : p ≠ 0) (hpTop : p ≠ ⊤) :
    AEStronglyMeasurable (fun t => criticalSpatialNorm p (L.velocity t))
      (volume.restrict (Ioi (0 : ℝ))) := by
  have hs : Ioi (0 : ℝ) = ⋃ n : ℕ, Ioc (0 : ℝ) (n : ℝ) := by
    ext t
    constructor
    · intro ht
      obtain ⟨n, hn⟩ := exists_nat_gt t
      exact mem_iUnion.mpr ⟨n, ht, hn.le⟩
    · intro ht
      obtain ⟨n, hn⟩ := mem_iUnion.mp ht
      exact hn.1
  rw [hs]
  exact AEStronglyMeasurable.iUnion
    (fun n : ℕ => criticalPositive_spatialNorm_aestronglyMeasurable L p hp0 hpTop n)

theorem criticalPositive_spatialNorm_six_aestronglyMeasurable_Ioi
    {ν : ℝ} (L : CriticalPositiveSobolevFlow ν) :
    AEStronglyMeasurable (fun t => criticalSpatialNorm 6 (L.velocity t))
      (volume.restrict (Ioi (0 : ℝ))) :=
  criticalPositive_spatialNorm_aestronglyMeasurable_Ioi L 6 (by norm_num) (by norm_num)

end
end SingularClosure
