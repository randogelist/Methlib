import QuasiFeffermanB.RootContract
import QuasiFeffermanB.LHRestart
import SingularClosure.CriticalClassicalWeakMomentum
import SingularClosure.CriticalPositiveFlow

/-! Actual weak-gradient identification and physical tail energy equality.
The smooth reference is an actual positive-time classical NSE solution.
No energy equality or derivative-identification certificate is assumed.
-/

set_option autoImplicit false
set_option Elab.async true

open Set Filter MeasureTheory
open scoped BigOperators ENNReal Topology Interval ContDiff

namespace QuasiFeffermanB
open SingularClosure
noncomputable section

theorem tail_physicalEnergy_congr_ae {v w : Field}
    (h : v =ᵐ[volume.restrict unitCube] w) : physicalEnergy v = physicalEnergy w := by
  simp only [physicalEnergy_eq_integral_norm_sq]
  apply integral_congr_ae
  filter_upwards [h] with x hx
  rw [hx]

theorem tail_physicalFieldInner_zero_of_ae_zero {v : Field}
    (hv : v =ᵐ[volume.restrict unitCube] (0 : Field)) (φ : Field) :
    physicalFieldInner v φ = 0 := by
  unfold physicalFieldInner
  calc
    (∫ x in unitCube, inner ℝ (v x) (φ x)) = ∫ _x in unitCube, (0 : ℝ) := by
      apply integral_congr_ae
      filter_upwards [hv] with x hx
      simp only [hx, Pi.zero_apply, inner_zero_left]
    _ = 0 := by simp

/-- The actual H1 approximants suffice to identify a zero weak derivative;
no independent Fourier-inversion or density premise is required. -/
theorem physicalH1_gradient_column_zero_of_ae_zero
    {v : Field} {G : Vec → (Vec →L[ℝ] Vec)}
    (hv : CriticalPhysicalH1 v G)
    (hz : v =ᵐ[volume.restrict unitCube] (0 : Field)) (j : Fin 3) :
    (fun x => G x (unitVector j)) =ᵐ[volume.restrict unitCube] (0 : Field) := by
  obtain ⟨w, hw, hwp, _hvelocity, hderivative⟩ := hv.approximation
  let g : Field := fun x => G x (unitVector j)
  have hg : MemLp g 2 (volume.restrict unitCube) :=
    (ContinuousLinearMap.apply ℝ Vec (unitVector j)).comp_memLp' hv.derivative_L2
  have hD2 (n : ℕ) : MemLp (fderiv ℝ (w n)) 2 (volume.restrict unitCube) :=
    critical_continuous_memLp_cube _ ((hw n).continuous_fderiv (by simp)) 2
  have hzero (n : ℕ) : physicalFieldInner (coordinateDerivative (w n) j) g = 0 := by
    have h := hv.weakGradient.integration_by_parts (coordinateDerivative (w n) j)
      (coordinateDerivative_smooth (hw n) j)
      (coordinateDerivative_spatialPeriodic j (w n) (hwp n)) j
    rw [tail_physicalFieldInner_zero_of_ae_zero hz] at h
    rw [critical_physicalFieldInner_comm]
    change physicalFieldInner g (coordinateDerivative (w n) j) = 0
    change 0 = -physicalFieldInner g (coordinateDerivative (w n) j) at h
    linarith
  have hlim : Tendsto (fun n => physicalFieldInner (coordinateDerivative (w n) j) g)
      atTop (𝓝 (physicalFieldInner g g)) := by
    change Tendsto (fun n => physicalFieldInner
      (fun x => fderiv ℝ (w n) x (unitVector j)) g) atTop
      (𝓝 (physicalFieldInner (fun x => G x (unitVector j)) g))
    simpa only [Function.comp_def, ContinuousLinearMap.apply_apply] using
      critical_physicalFieldInner_compCLM_tendsto
        (ContinuousLinearMap.apply ℝ Vec (unitVector j))
        (fun n => fderiv ℝ (w n)) G g hD2 hv.derivative_L2 hg hderivative
  have hlimzero : Tendsto
      (fun n => physicalFieldInner (coordinateDerivative (w n) j) g)
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [hzero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  have hself : physicalFieldInner g g = 0 := tendsto_nhds_unique hlim hlimzero
  rw [critical_physicalFieldInner_eq_L2_inner g g hg hg,
    real_inner_self_eq_norm_sq] at hself
  have hLp : hg.toLp g = 0 := by
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg (hg.toLp g)]
  have hae : (hg.toLp g : Field) =ᵐ[volume.restrict unitCube] (0 : Field) := by
    rw [hLp]
    exact Lp.coeFn_zero Vec 2 (volume.restrict unitCube)
  exact hg.coeFn_toLp.symm.trans hae

theorem physicalH1_gradient_zero_of_ae_zero
    {v : Field} {G : Vec → (Vec →L[ℝ] Vec)}
    (hv : CriticalPhysicalH1 v G)
    (hz : v =ᵐ[volume.restrict unitCube] (0 : Field)) :
    G =ᵐ[volume.restrict unitCube] (0 : Vec → (Vec →L[ℝ] Vec)) := by
  have hall : ∀ᵐ x ∂volume.restrict unitCube, ∀ j : Fin 3, G x (unitVector j) = 0 :=
    ae_all_iff.mpr (fun j => physicalH1_gradient_column_zero_of_ae_zero hv hz j)
  filter_upwards [hall] with x hx
  apply ContinuousLinearMap.ext
  intro z
  change G x z = 0
  rw [← sum_coordinate_unitVector z, map_sum]
  simp only [map_smul, hx, smul_zero, Finset.sum_const_zero]

/-- Every native weak derivative agrees a.e. with the actual smooth derivative
when the velocity representatives agree a.e. -/
theorem physicalH1_gradient_eq_smooth
    {u v : Field} {G : Vec → (Vec →L[ℝ] Vec)}
    (hu : CriticalPhysicalH1 u G)
    (hv : ContDiff ℝ ∞ v) (hvp : SpatialPeriodic v)
    (heq : u =ᵐ[volume.restrict unitCube] v) :
    G =ᵐ[volume.restrict unitCube] fderiv ℝ v := by
  have hsub := hu.sub_smooth v hv hvp
  have hz : u - v =ᵐ[volume.restrict unitCube] (0 : Field) := by
    filter_upwards [heq] with x hx
    simp only [Pi.sub_apply, Pi.zero_apply, hx, sub_self]
  have hG := physicalH1_gradient_zero_of_ae_zero hsub hz
  filter_upwards [hG] with x hx
  change G x - fderiv ℝ v x = 0 at hx
  exact sub_eq_zero.mp hx

theorem tail_criticalGradientEnergy_congr_ae
    {G H : Vec → (Vec →L[ℝ] Vec)}
    (heq : G =ᵐ[volume.restrict unitCube] H) :
    criticalGradientEnergy G = criticalGradientEnergy H := by
  unfold criticalGradientEnergy
  apply Finset.sum_congr rfl
  intro j hj
  apply tail_physicalEnergy_congr_ae
  filter_upwards [heq] with x hx
  rw [hx]

theorem physicalH1_gradientEnergy_eq_smooth
    {u v : Field} {G : Vec → (Vec →L[ℝ] Vec)}
    (hu : CriticalPhysicalH1 u G)
    (hv : ContDiff ℝ ∞ v) (hvp : SpatialPeriodic v)
    (heq : u =ᵐ[volume.restrict unitCube] v) :
    criticalGradientEnergy G = physicalDissipation v := by
  rw [tail_criticalGradientEnergy_congr_ae
    (physicalH1_gradient_eq_smooth hu hv hvp heq)]
  exact criticalGradientEnergy_fderiv v hv

theorem positiveSmoothNSE_test
    {ν : ℝ} {v : Velocity} {p : Pressure} (hv : PositiveSmoothNSE ν v p) :
    CriticalPositiveSolenoidalTest v :=
  ⟨hv.velocity_smooth, hv.velocity_periodic, hv.divergence_free⟩

theorem positiveSmoothNSE_pressure_spatial_smooth
    {ν : ℝ} {v : Velocity} {p : Pressure} (hv : PositiveSmoothNSE ν v p)
    {t : ℝ} (ht : 0 < t) : ContDiff ℝ ∞ (p t) := by
  rw [← contDiffOn_univ]
  exact hv.pressure_smooth.comp (contDiff_const.prodMk contDiff_id).contDiffOn
    (fun x _ => ht)

/-- Exact tail energy equality of the original LH path, obtained from an
actual positive-time classical reference and its spatial a.e. identification.
The reference is only required after the earlier time s; δ must be later. -/
theorem LH_TAIL_ENERGY_OF_POSITIVE_REFERENCE
    {ν : ℝ} {a : CriticalPhysicalL2} {u : Velocity} {G : WeakGradientTrajectory}
    (hν : 0 < ν) (hu : CriticalLerayHopf ν a u G)
    {v : Velocity} {p : Pressure} (hv : PositiveSmoothNSE ν v p)
    {s δ : ℝ} (hs : 0 ≤ s) (hδ : s < δ)
    (heq : ∀ r : ℝ, s < r →
      u r =ᵐ[volume.restrict unitCube] v (r - s)) :
    TailEnergyEquality ν u G δ := by
  intro t ht
  have ht0 : 0 < t := lt_of_lt_of_le (lt_of_le_of_lt hs hδ) ht
  have htest := positiveSmoothNSE_test hv
  have hclassical := CRITICAL_SMOOTH_NSE_ENERGY_IDENTITY ν v p htest
    (fun r hr => positiveSmoothNSE_pressure_spatial_smooth hv hr)
    hv.pressure_periodic hv.equation hν (δ - s) (t - s)
    (sub_pos.mpr hδ) (sub_le_sub_right ht s)
  have hH1 := (ae_restrict_iff' measurableSet_Ioc).mp (hu.spatial_H1 t ht0)
  have hD : (fun r => criticalGradientEnergy (G r))
      =ᵐ[volume.restrict (uIoc δ t)] (fun r => physicalDissipation (v (r - s))) := by
    rw [uIoc_of_le ht]
    apply (ae_restrict_iff' measurableSet_Ioc).mpr
    filter_upwards [hH1] with r hr
    intro hrs
    have hsr : s < r := hδ.trans hrs.1
    exact physicalH1_gradientEnergy_eq_smooth
      (hr ⟨hs.trans_lt hsr, hrs.2⟩)
      (htest.spatial_smooth (sub_pos.mpr hsr))
      (hv.velocity_periodic (r - s) (sub_pos.mpr hsr)) (heq r hsr)
  have hDint : (∫ r in δ..t, criticalGradientEnergy (G r)) =
      ∫ r in (δ - s)..(t - s), physicalDissipation (v r) := by
    rw [intervalIntegral.integral_congr_ae_restrict hD,
      intervalIntegral.integral_comp_sub_right (fun r => physicalDissipation (v r)) s]
  rw [tail_physicalEnergy_congr_ae (heq t (hδ.trans_le ht)),
    tail_physicalEnergy_congr_ae (heq δ hδ), hDint]
  exact hclassical.2

theorem LH_TAIL_ENERGY_OF_POSITIVE_FLOW
    {ν : ℝ} {a : CriticalPhysicalL2} {u : Velocity} {G : WeakGradientTrajectory}
    (hν : 0 < ν) (hu : CriticalLerayHopf ν a u G)
    (L : CriticalPositiveSobolevFlow ν)
    {s δ : ℝ} (hs : 0 ≤ s) (hδ : s < δ)
    (heq : ∀ r : ℝ, s < r →
      u r =ᵐ[volume.restrict unitCube] L.velocity (r - s)) :
    TailEnergyEquality ν u G δ :=
  LH_TAIL_ENERGY_OF_POSITIVE_REFERENCE hν hu (CRITICAL_POSITIVE_PHYSICAL_NSE L)
    hs hδ heq

/-- A tail energy identity gives restart membership at every tail endpoint,
without imposing an H1 condition on the arbitrary gradient representative
at that single time. -/
theorem LH_RESTART_OF_TAIL_ENERGY
    {ν : ℝ} {a : CriticalPhysicalL2} {u : Velocity} {G : WeakGradientTrajectory}
    (hν : 0 ≤ ν) (hu : CriticalLerayHopf ν a u G)
    {δ : ℝ} (hδ : 0 ≤ δ) (hE : TailEnergyEquality ν u G δ) :
    CriticalLerayHopf ν (criticalL2Representative (u δ))
      (Shift δ u) (fun t => G (δ + t)) := by
  have hvelocity : timeTranslate δ u = Shift δ u := by
    funext t
    change u (t + δ) = u (δ + t)
    exact congrArg u (add_comm t δ)
  have hgradient : timeTranslate δ G = (fun t => G (δ + t)) := by
    funext t
    change G (t + δ) = G (δ + t)
    exact congrArg G (add_comm t δ)
  have hrestart :=
    LH_RESTART_FROM_ENERGY_START hu hν hδ (fun t ht => (hE t ht).le)
  rw [hvelocity, hgradient] at hrestart
  exact hrestart

end
end QuasiFeffermanB
