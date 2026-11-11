import SingularClosure.CoordinateAverageCalculus
import SingularClosure.CoordinateAverageOrthogonal

/-!
# Six concrete channels on smooth periodic physical fields

The fixed axes are the third coordinate followed by the first. The three
primary channels are the horizontal averaged field, the vertical averaged
field, and the averaging remainder. Each is refined by the first-coordinate
average and its complement. All maps below act on the literal physical lifts.
-/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory
open scoped BigOperators ContDiff

namespace SingularClosure

noncomputable section

def verticalComponentCLM : Vec →L[ℝ] Vec :=
  (EuclideanSpace.proj (2 : Fin 3)).smulRight (unitVector 2)

def verticalComponent (a : Field) : Field := fun x => verticalComponentCLM (a x)

def baseChannelV (a : Field) : Field :=
  coordinateAverage 2 a - verticalComponent (coordinateAverage 2 a)

def baseChannelW (a : Field) : Field := verticalComponent (coordinateAverage 2 a)

def baseChannelR (a : Field) : Field := a - coordinateAverage 2 a

def smoothSixChannel (A : Fin 6) (a : Field) : Field :=
  ![coordinateAverage 0 (baseChannelV a),
    baseChannelV a - coordinateAverage 0 (baseChannelV a),
    coordinateAverage 0 (baseChannelW a),
    baseChannelW a - coordinateAverage 0 (baseChannelW a),
    coordinateAverage 0 (baseChannelR a),
    baseChannelR a - coordinateAverage 0 (baseChannelR a)] A

theorem SMOOTH_SIX_CHANNEL_RECONSTRUCTION (a : Field) :
    (∑ A : Fin 6, smoothSixChannel A a) = a := by
  simp [smoothSixChannel, Fin.sum_univ_succ, baseChannelV, baseChannelW, baseChannelR] <;> abel

theorem spatialPeriodic_sub {a b : Field}
    (ha : SpatialPeriodic a) (hb : SpatialPeriodic b) : SpatialPeriodic (a - b) := by
  intro x i
  change a (x + unitVector i) - b (x + unitVector i) = a x - b x
  rw [ha, hb]

theorem verticalComponent_smooth {a : Field} (ha : ContDiff ℝ ∞ a) :
    ContDiff ℝ ∞ (verticalComponent a) := verticalComponentCLM.contDiff.comp ha

theorem verticalComponent_periodic {a : Field} (ha : SpatialPeriodic a) :
    SpatialPeriodic (verticalComponent a) := by
  intro x i
  unfold verticalComponent
  rw [ha]

theorem verticalComponent_coordinateDerivative {a : Field}
    (ha : ContDiff ℝ ∞ a) (i : Fin 3) :
    coordinateDerivative (verticalComponent a) i =
      verticalComponent (coordinateDerivative a i) := by
  funext x
  have h := verticalComponentCLM.hasFDerivAt.comp x
    ((ha.differentiable (by simp)) x).hasFDerivAt
  unfold coordinateDerivative verticalComponent
  rw [h.fderiv]
  rfl

theorem coordinateDerivative_sub_smooth {a b : Field}
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (i : Fin 3) :
    coordinateDerivative (a - b) i = coordinateDerivative a i - coordinateDerivative b i := by
  funext x
  unfold coordinateDerivative
  rw [fderiv_sub ((ha.differentiable (by simp)) x) ((hb.differentiable (by simp)) x)]
  rfl

theorem divergence_sub_smooth {a b : Field}
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (x : Vec) :
    divergence (a - b) x = divergence a x - divergence b x := by
  simp only [divergence, coordinateDerivative_sub_smooth ha hb,
    Pi.sub_apply, PiLp.sub_apply, Finset.sum_sub_distrib]

theorem baseChannelV_smooth {a : Field} (ha : ContDiff ℝ ∞ a) :
    ContDiff ℝ ∞ (baseChannelV a) :=
  (coordinateAverage_smooth 2 a ha).sub
    (verticalComponent_smooth (coordinateAverage_smooth 2 a ha))

theorem baseChannelW_smooth {a : Field} (ha : ContDiff ℝ ∞ a) :
    ContDiff ℝ ∞ (baseChannelW a) :=
  verticalComponent_smooth (coordinateAverage_smooth 2 a ha)

theorem baseChannelR_smooth {a : Field} (ha : ContDiff ℝ ∞ a) :
    ContDiff ℝ ∞ (baseChannelR a) := ha.sub (coordinateAverage_smooth 2 a ha)

theorem baseChannelV_periodic {a : Field} (ha : SpatialPeriodic a) :
    SpatialPeriodic (baseChannelV a) :=
  spatialPeriodic_sub (coordinateAverage_periodic 2 a ha)
    (verticalComponent_periodic (coordinateAverage_periodic 2 a ha))

theorem baseChannelW_periodic {a : Field} (ha : SpatialPeriodic a) :
    SpatialPeriodic (baseChannelW a) :=
  verticalComponent_periodic (coordinateAverage_periodic 2 a ha)

theorem baseChannelR_periodic {a : Field} (ha : SpatialPeriodic a) :
    SpatialPeriodic (baseChannelR a) := spatialPeriodic_sub ha (coordinateAverage_periodic 2 a ha)

theorem smoothSixChannel_smooth (A : Fin 6) (a : Field) (ha : ContDiff ℝ ∞ a) :
    ContDiff ℝ ∞ (smoothSixChannel A a) := by
  have hv := baseChannelV_smooth ha
  have hw := baseChannelW_smooth ha
  have hr := baseChannelR_smooth ha
  fin_cases A
  · exact coordinateAverage_smooth 0 _ hv
  · exact hv.sub (coordinateAverage_smooth 0 _ hv)
  · exact coordinateAverage_smooth 0 _ hw
  · exact hw.sub (coordinateAverage_smooth 0 _ hw)
  · exact coordinateAverage_smooth 0 _ hr
  · exact hr.sub (coordinateAverage_smooth 0 _ hr)

theorem smoothSixChannel_periodic (A : Fin 6) (a : Field) (ha : SpatialPeriodic a) :
    SpatialPeriodic (smoothSixChannel A a) := by
  have hv := baseChannelV_periodic ha
  have hw := baseChannelW_periodic ha
  have hr := baseChannelR_periodic ha
  fin_cases A
  · exact coordinateAverage_periodic 0 _ hv
  · exact spatialPeriodic_sub hv (coordinateAverage_periodic 0 _ hv)
  · exact coordinateAverage_periodic 0 _ hw
  · exact spatialPeriodic_sub hw (coordinateAverage_periodic 0 _ hw)
  · exact coordinateAverage_periodic 0 _ hr
  · exact spatialPeriodic_sub hr (coordinateAverage_periodic 0 _ hr)

theorem verticalComponent_divergence {a : Field} (ha : ContDiff ℝ ∞ a) (x : Vec) :
    divergence (verticalComponent a) x = coordinateDerivative a 2 x 2 := by
  simp only [divergence, verticalComponent_coordinateDerivative ha]
  simp [verticalComponent, verticalComponentCLM, unitVector, Fin.sum_univ_succ]

theorem baseChannelW_divergence_zero (a : Field) (ha : ContDiff ℝ ∞ a) (x : Vec) :
    divergence (baseChannelW a) x = 0 := by
  rw [baseChannelW, verticalComponent_divergence (coordinateAverage_smooth 2 a ha),
    coordinateAverage_own_coordinateDerivative_zero]
  rfl

theorem baseChannelV_divergence_zero (a : Field)
    (ha : ContDiff ℝ ∞ a) (hp : SpatialPeriodic a)
    (hd : ∀ x : Vec, divergence a x = 0) (x : Vec) :
    divergence (baseChannelV a) x = 0 := by
  change divergence (coordinateAverage 2 a - baseChannelW a) x = 0
  rw [divergence_sub_smooth (coordinateAverage_smooth 2 a ha) (baseChannelW_smooth ha),
    coordinateAverage_divergence_free 2 a ha hp hd, baseChannelW_divergence_zero a ha,
    sub_self]

theorem baseChannelR_divergence_zero (a : Field)
    (ha : ContDiff ℝ ∞ a) (hp : SpatialPeriodic a)
    (hd : ∀ x : Vec, divergence a x = 0) (x : Vec) :
    divergence (baseChannelR a) x = 0 := by
  rw [baseChannelR, divergence_sub_smooth ha (coordinateAverage_smooth 2 a ha),
    hd, coordinateAverage_divergence_free 2 a ha hp hd, sub_self]

theorem smoothSixChannel_divergence_zero (A : Fin 6) (a : Field)
    (ha : ContDiff ℝ ∞ a) (hp : SpatialPeriodic a)
    (hd : ∀ x : Vec, divergence a x = 0) (x : Vec) :
    divergence (smoothSixChannel A a) x = 0 := by
  have hv := baseChannelV_divergence_zero a ha hp hd
  have hw := baseChannelW_divergence_zero a ha
  have hr := baseChannelR_divergence_zero a ha hp hd
  have hvs := baseChannelV_smooth ha
  have hws := baseChannelW_smooth ha
  have hrs := baseChannelR_smooth ha
  have hvp := baseChannelV_periodic hp
  have hwp := baseChannelW_periodic hp
  have hrp := baseChannelR_periodic hp
  fin_cases A
  · exact coordinateAverage_divergence_free 0 _ hvs hvp hv x
  · change divergence (baseChannelV a - coordinateAverage 0 (baseChannelV a)) x = 0
    rw [divergence_sub_smooth hvs (coordinateAverage_smooth 0 _ hvs), hv,
      coordinateAverage_divergence_free 0 _ hvs hvp hv, sub_self]
  · exact coordinateAverage_divergence_free 0 _ hws hwp hw x
  · change divergence (baseChannelW a - coordinateAverage 0 (baseChannelW a)) x = 0
    rw [divergence_sub_smooth hws (coordinateAverage_smooth 0 _ hws), hw,
      coordinateAverage_divergence_free 0 _ hws hwp hw, sub_self]
  · exact coordinateAverage_divergence_free 0 _ hrs hrp hr x
  · change divergence (baseChannelR a - coordinateAverage 0 (baseChannelR a)) x = 0
    rw [divergence_sub_smooth hrs (coordinateAverage_smooth 0 _ hrs), hr,
      coordinateAverage_divergence_free 0 _ hrs hrp hr, sub_self]

theorem meanZero_sub {a b : Field} (ha : MeanZero a) (hb : MeanZero b) :
    MeanZero (a - b) := by
  refine ⟨ha.1.sub hb.1, ?_⟩
  unfold spatialMean
  rw [integral_sub ha.1 hb.1]
  change spatialMean a - spatialMean b = 0
  rw [ha.2, hb.2, sub_self]

theorem verticalComponent_meanZero {a : Field} (ha : MeanZero a) :
    MeanZero (verticalComponent a) := by
  refine ⟨verticalComponentCLM.integrable_comp ha.1, ?_⟩
  unfold spatialMean verticalComponent
  rw [verticalComponentCLM.integral_comp_comm ha.1]
  change verticalComponentCLM (spatialMean a) = 0
  rw [ha.2, map_zero]

theorem smoothSixChannel_meanZero (A : Fin 6) (a : Field)
    (ha : ContDiff ℝ ∞ a) (hm : MeanZero a) : MeanZero (smoothSixChannel A a) := by
  have havg := coordinateAverage_preserves_meanZero 2 a ha.continuous hm
  have hw : MeanZero (baseChannelW a) := verticalComponent_meanZero havg
  have hv : MeanZero (baseChannelV a) := meanZero_sub havg hw
  have hr : MeanZero (baseChannelR a) := meanZero_sub hm havg
  fin_cases A
  · exact coordinateAverage_preserves_meanZero 0 _ (baseChannelV_smooth ha).continuous hv
  · exact meanZero_sub hv
      (coordinateAverage_preserves_meanZero 0 _ (baseChannelV_smooth ha).continuous hv)
  · exact coordinateAverage_preserves_meanZero 0 _ (baseChannelW_smooth ha).continuous hw
  · exact meanZero_sub hw
      (coordinateAverage_preserves_meanZero 0 _ (baseChannelW_smooth ha).continuous hw)
  · exact coordinateAverage_preserves_meanZero 0 _ (baseChannelR_smooth ha).continuous hr
  · exact meanZero_sub hr
      (coordinateAverage_preserves_meanZero 0 _ (baseChannelR_smooth ha).continuous hr)

theorem smoothSixChannel_preserves_smoothSigmaZero (A : Fin 6) (a : Field)
    (ha : SmoothSigmaZero a) : SmoothSigmaZero (smoothSixChannel A a) :=
  ⟨smoothSixChannel_smooth A a ha.smooth,
    smoothSixChannel_periodic A a ha.periodic,
    smoothSixChannel_divergence_zero A a ha.smooth ha.periodic ha.divergence_free,
    smoothSixChannel_meanZero A a ha.smooth ha.mean_zero⟩

theorem baseChannelW_coordinateDerivative (i : Fin 3) (a : Field)
    (ha : ContDiff ℝ ∞ a) (hp : SpatialPeriodic a) :
    coordinateDerivative (baseChannelW a) i = baseChannelW (coordinateDerivative a i) := by
  unfold baseChannelW
  rw [verticalComponent_coordinateDerivative (coordinateAverage_smooth 2 a ha),
    coordinateAverage_all_coordinateDerivative_commute i 2 a ha hp]

theorem baseChannelV_coordinateDerivative (i : Fin 3) (a : Field)
    (ha : ContDiff ℝ ∞ a) (hp : SpatialPeriodic a) :
    coordinateDerivative (baseChannelV a) i = baseChannelV (coordinateDerivative a i) := by
  change coordinateDerivative (coordinateAverage 2 a - baseChannelW a) i = _
  rw [coordinateDerivative_sub_smooth (coordinateAverage_smooth 2 a ha)
    (baseChannelW_smooth ha), coordinateAverage_all_coordinateDerivative_commute i 2 a ha hp,
    baseChannelW_coordinateDerivative i a ha hp]
  rfl

theorem baseChannelR_coordinateDerivative (i : Fin 3) (a : Field)
    (ha : ContDiff ℝ ∞ a) (hp : SpatialPeriodic a) :
    coordinateDerivative (baseChannelR a) i = baseChannelR (coordinateDerivative a i) := by
  unfold baseChannelR
  rw [coordinateDerivative_sub_smooth ha (coordinateAverage_smooth 2 a ha),
    coordinateAverage_all_coordinateDerivative_commute i 2 a ha hp]

theorem smoothSixChannel_coordinateDerivative (A : Fin 6) (i : Fin 3) (a : Field)
    (ha : ContDiff ℝ ∞ a) (hp : SpatialPeriodic a) :
    coordinateDerivative (smoothSixChannel A a) i =
      smoothSixChannel A (coordinateDerivative a i) := by
  have hv := baseChannelV_smooth ha
  have hw := baseChannelW_smooth ha
  have hr := baseChannelR_smooth ha
  have hvp := baseChannelV_periodic hp
  have hwp := baseChannelW_periodic hp
  have hrp := baseChannelR_periodic hp
  fin_cases A
  · change coordinateDerivative (coordinateAverage 0 (baseChannelV a)) i = _
    rw [coordinateAverage_all_coordinateDerivative_commute i 0 _ hv hvp,
      baseChannelV_coordinateDerivative i a ha hp]
    rfl
  · change coordinateDerivative (baseChannelV a - coordinateAverage 0 (baseChannelV a)) i = _
    rw [coordinateDerivative_sub_smooth hv (coordinateAverage_smooth 0 _ hv),
      coordinateAverage_all_coordinateDerivative_commute i 0 _ hv hvp,
      baseChannelV_coordinateDerivative i a ha hp]
    rfl
  · change coordinateDerivative (coordinateAverage 0 (baseChannelW a)) i = _
    rw [coordinateAverage_all_coordinateDerivative_commute i 0 _ hw hwp,
      baseChannelW_coordinateDerivative i a ha hp]
    rfl
  · change coordinateDerivative (baseChannelW a - coordinateAverage 0 (baseChannelW a)) i = _
    rw [coordinateDerivative_sub_smooth hw (coordinateAverage_smooth 0 _ hw),
      coordinateAverage_all_coordinateDerivative_commute i 0 _ hw hwp,
      baseChannelW_coordinateDerivative i a ha hp]
    rfl
  · change coordinateDerivative (coordinateAverage 0 (baseChannelR a)) i = _
    rw [coordinateAverage_all_coordinateDerivative_commute i 0 _ hr hrp,
      baseChannelR_coordinateDerivative i a ha hp]
    rfl
  · change coordinateDerivative (baseChannelR a - coordinateAverage 0 (baseChannelR a)) i = _
    rw [coordinateDerivative_sub_smooth hr (coordinateAverage_smooth 0 _ hr),
      coordinateAverage_all_coordinateDerivative_commute i 0 _ hr hrp,
      baseChannelR_coordinateDerivative i a ha hp]
    rfl

end

end SingularClosure
