import SingularClosure.CriticalPositiveFlow
import SingularClosure.CoordinateAverageOrthogonal
import SingularClosure.PeriodicFourierInjective
import SingularClosure.PeriodicSobolev

/-! Uniqueness of the actual normalized pressure.
Equality of the positive-time velocity, including cube-a.e. equality between
smooth periodic representatives, determines the pressure pointwise.
-/

set_option autoImplicit false
set_option Elab.async true

open Set Filter MeasureTheory
open scoped BigOperators ContDiff Topology

namespace QuasiFeffermanB
open SingularClosure
noncomputable section

theorem pressure_integral_cube_constant (c : ℝ) :
    (∫ _x : Vec in unitCube, c) = c := by
  rw [integral_unitCube_productMeasure]
  simp

theorem pressure_fderiv_eq_of_gradient_eq
    {p q : Vec → ℝ} (h : ∀ x : Vec, gradient p x = gradient q x) :
    ∀ x : Vec, fderiv ℝ p x = fderiv ℝ q x := by
  intro x
  apply ContinuousLinearMap.ext
  intro z
  rw [← sum_coordinate_unitVector z, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [map_smul]
  apply congrArg (fun r : ℝ => z i • r)
  exact congrArg (fun y : Vec => y i) (h x)

/-- On connected Euclidean space, equal gradients determine a smooth scalar
function up to a constant; the two actual zero means remove that constant. -/
theorem NORMALIZED_PRESSURE_UNIQUE_OF_GRADIENT
    {p q : Vec → ℝ} (hp : ContDiff ℝ ∞ p) (hq : ContDiff ℝ ∞ q)
    (hpm : PressureMeanZero p) (hqm : PressureMeanZero q)
    (hgrad : ∀ x : Vec, gradient p x = gradient q x) : p = q := by
  have hpd : Differentiable ℝ p := hp.differentiable (by simp)
  have hqd : Differentiable ℝ q := hq.differentiable (by simp)
  have hfd := pressure_fderiv_eq_of_gradient_eq hgrad
  have hzero (x : Vec) : fderiv ℝ (fun y => p y - q y) x = 0 := by
    rw [fderiv_fun_sub (hpd x) (hqd x), hfd x, sub_self]
  have hconstant (x : Vec) : p x - q x = p 0 - q 0 :=
    is_const_of_fderiv_eq_zero (hpd.sub hqd) hzero x 0
  have hint : (∫ x in unitCube, p x - q x) = 0 := by
    rw [integral_sub hpm.1 hqm.1, hpm.2, hqm.2, sub_self]
  have hc : p 0 - q 0 = 0 := by
    calc
      p 0 - q 0 = ∫ _x : Vec in unitCube, p 0 - q 0 :=
        (pressure_integral_cube_constant _).symm
      _ = ∫ x in unitCube, p x - q x := by
        apply integral_congr_ae
        exact Eventually.of_forall (fun x => (hconstant x).symm)
      _ = 0 := hint
  funext x
  exact sub_eq_zero.mp ((hconstant x).trans hc)

theorem pressure_unique_spatial_smooth
    {ν : ℝ} {u : Velocity} {p : Pressure}
    (hu : PositiveSmoothNSE ν u p) {t : ℝ} (ht : 0 < t) :
    ContDiff ℝ ∞ (p t) := by
  rw [← contDiffOn_univ]
  exact hu.pressure_smooth.comp (contDiff_const.prodMk contDiff_id).contDiffOn
    (fun x _ => ht)

theorem pressure_unique_velocity_spatial_smooth
    {ν : ℝ} {u : Velocity} {p : Pressure}
    (hu : PositiveSmoothNSE ν u p) {t : ℝ} (ht : 0 < t) :
    ContDiff ℝ ∞ (u t) := by
  rw [← contDiffOn_univ]
  exact hu.velocity_smooth.comp (contDiff_const.prodMk contDiff_id).contDiffOn
    (fun x _ => ht)

theorem pressure_timeDerivative_eq_of_positive_velocity_eq
    {u v : Velocity} (heq : ∀ t : ℝ, 0 < t → u t = v t)
    {t : ℝ} (ht : 0 < t) (x : Vec) :
    timeDerivative u t x = timeDerivative v t x := by
  unfold timeDerivative
  apply Filter.EventuallyEq.derivWithin_eq_of_nhds
  filter_upwards [isOpen_Ioi.mem_nhds ht] with r hr
  exact congrFun (heq r hr) x

/-- Two actual positive-time NSE solutions with identical positive-time
velocity have identical normalized pressure, without an analytic premise. -/
theorem POSITIVE_SMOOTH_NSE_NORMALIZED_PRESSURE_UNIQUE
    {ν : ℝ} {u v : Velocity} {p q : Pressure}
    (hu : PositiveSmoothNSE ν u p) (hv : PositiveSmoothNSE ν v q)
    (heq : ∀ t : ℝ, 0 < t → u t = v t) :
    ∀ t : ℝ, 0 < t → p t = q t := by
  intro t ht
  apply NORMALIZED_PRESSURE_UNIQUE_OF_GRADIENT
    (pressure_unique_spatial_smooth hu ht) (pressure_unique_spatial_smooth hv ht)
    (hu.pressure_mean_zero t ht) (hv.pressure_mean_zero t ht)
  intro x
  have hpu := hu.equation t ht x
  have hpv := hv.equation t ht x
  rw [pressure_timeDerivative_eq_of_positive_velocity_eq heq ht x, heq t ht] at hpu
  exact add_left_cancel (hpu.trans hpv.symm)

theorem POSITIVE_SMOOTH_NSE_PRESSURE_UNIQUE
    {ν : ℝ} {u : Velocity} {p q : Pressure}
    (hp : PositiveSmoothNSE ν u p) (hq : PositiveSmoothNSE ν u q) :
    ∀ t : ℝ, 0 < t → p t = q t :=
  POSITIVE_SMOOTH_NSE_NORMALIZED_PRESSURE_UNIQUE hp hq (fun _ _ => rfl)

theorem continuous_periodic_velocity_eq_of_cube_ae
    {u v : Field} (hu : Continuous u) (hv : Continuous v)
    (hup : SpatialPeriodic u) (hvp : SpatialPeriodic v)
    (heq : u =ᵐ[volume.restrict unitCube] v) : u = v := by
  apply datumFourierCoeff_injective_continuous_periodic u v hu hv hup hvp
  funext k i
  unfold datumFourierCoeff
  apply integral_congr_ae
  filter_upwards [heq] with x hx
  simp only [datumFourierIntegrand, hx]

/-- The physically relevant equality convention is cube-a.e. equality at each
positive time; smooth periodicity upgrades it before pressure identification. -/
theorem POSITIVE_SMOOTH_NSE_NORMALIZED_PRESSURE_UNIQUE_OF_AE
    {ν : ℝ} {u v : Velocity} {p q : Pressure}
    (hu : PositiveSmoothNSE ν u p) (hv : PositiveSmoothNSE ν v q)
    (heq : ∀ t : ℝ, 0 < t → u t =ᵐ[volume.restrict unitCube] v t) :
    ∀ t : ℝ, 0 < t → p t = q t := by
  apply POSITIVE_SMOOTH_NSE_NORMALIZED_PRESSURE_UNIQUE hu hv
  intro t ht
  exact continuous_periodic_velocity_eq_of_cube_ae
    (pressure_unique_velocity_spatial_smooth hu ht).continuous
    (pressure_unique_velocity_spatial_smooth hv ht).continuous
    (hu.velocity_periodic t ht) (hv.velocity_periodic t ht) (heq t ht)

end
end QuasiFeffermanB
