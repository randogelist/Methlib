import QuasiFeffermanB.TailEnergy
import QuasiFeffermanB.TailRegularity
import SingularClosure.CriticalSerrinUniqueness

/-! Uniqueness from every regular tail trace.
The original LH gradient representative is retained. Strong trace transfers
from its proved energy restart to the actual shifted classical reference.
-/

set_option autoImplicit false
set_option Elab.async true

open Set Filter MeasureTheory
open scoped ContDiff ENNReal Topology Interval

namespace QuasiFeffermanB
open SingularClosure
noncomputable section

theorem positiveSmoothNSE_timeTranslate
    {ν : ℝ} {v : Velocity} {p : Pressure}
    (hv : PositiveSmoothNSE ν v p) {ε : ℝ} (hε : 0 ≤ ε) :
    PositiveSmoothNSE ν (timeTranslate ε v) (timeTranslate ε p) := by
  have hpositive (t : ℝ) (ht : 0 < t) : 0 < t + ε := by linarith
  have hmap : MapsTo (fun z : ℝ × Vec => (z.1 + ε, z.2))
      positiveSpacetime positiveSpacetime := by
    intro z hz
    exact hpositive z.1 hz
  have hcont : ContDiff ℝ ∞ (fun z : ℝ × Vec => (z.1 + ε, z.2)) :=
    (contDiff_fst.add contDiff_const).prodMk contDiff_snd
  refine {
    velocity_smooth := hv.velocity_smooth.comp hcont.contDiffOn hmap
    pressure_smooth := hv.pressure_smooth.comp hcont.contDiffOn hmap
    velocity_periodic := fun t ht => hv.velocity_periodic (t + ε) (hpositive t ht)
    pressure_periodic := fun t ht => hv.pressure_periodic (t + ε) (hpositive t ht)
    divergence_free := fun t ht => hv.divergence_free (t + ε) (hpositive t ht)
    equation := ?_
    velocity_mean_zero := fun t ht => hv.velocity_mean_zero (t + ε) (hpositive t ht)
    pressure_mean_zero := fun t ht => hv.pressure_mean_zero (t + ε) (hpositive t ht)
  }
  intro t ht x
  have hd : timeDerivative (timeTranslate ε v) t x = timeDerivative v (t + ε) x := by
    simpa only [timeTranslate, sub_neg_eq_add] using
      positive_timeDerivative_translate hv (-ε) t ht
        (by simpa only [sub_neg_eq_add] using hpositive t ht) x
  rw [hd]
  exact hv.equation (t + ε) (hpositive t ht) x

theorem positive_reference_shifted_serrin
    {v : Velocity} {ε : ℝ} (hε : 0 ≤ ε)
    (hSerrin : ∀ T : ℝ, 0 < T →
      MemLp (fun t => criticalSpatialNorm 6 (v t)) 4
        (volume.restrict (Ioc (0 : ℝ) T)))
    (T : ℝ) (hT : 0 < T) :
    MemLp (fun t => criticalSpatialNorm 6 (timeTranslate ε v t)) 4
      (volume.restrict (Ioc (0 : ℝ) T)) :=
  timeTranslate_memLp_Ioc hε (hSerrin (T + ε) (by linarith))

theorem LH_UNIQUE_FUTURE_OF_POSITIVE_REFERENCE
    {ν : ℝ} {a : CriticalPhysicalL2} {u : Velocity} {G : WeakGradientTrajectory}
    (hν : 0 < ν) (hu : CriticalLerayHopf ν a u G)
    {v : Velocity} {p : Pressure} (hv : PositiveSmoothNSE ν v p)
    {s δ : ℝ} (hs : 0 ≤ s) (hδ : s < δ)
    (heq : ∀ r : ℝ, s < r →
      u r =ᵐ[volume.restrict unitCube] v (r - s))
    (hSerrin : ∀ T : ℝ, 0 < T →
      MemLp (fun t => criticalSpatialNorm 6 (v t)) 4
        (volume.restrict (Ioc (0 : ℝ) T))) :
    UniqueFuture ν u G δ := by
  have hδ0 : 0 ≤ δ := hs.trans hδ.le
  have henergy : TailEnergyEquality ν u G δ :=
    LH_TAIL_ENERGY_OF_POSITIVE_REFERENCE hν hu hv hs hδ heq
  have hrestart := LH_RESTART_OF_TAIL_ENERGY hν.le hu hδ0 henergy
  let ε : ℝ := δ - s
  have hε : 0 < ε := sub_pos.mpr hδ
  have hshift : PositiveSmoothNSE ν (timeTranslate ε v) (timeTranslate ε p) :=
    positiveSmoothNSE_timeTranslate hv hε.le
  have hagree (t : ℝ) (ht : 0 < t) :
      Shift δ u t =ᵐ[volume.restrict unitCube] timeTranslate ε v t := by
    have h := heq (δ + t) (by linarith)
    have he : δ + t - s = t + ε := by dsimp [ε]; ring
    simpa only [Shift, timeTranslate, he] using h
  have htrace : Tendsto (fun t => eLpNorm
      (timeTranslate ε v t - (criticalL2Representative (u δ) : Field))
      2 (volume.restrict unitCube)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    apply hrestart.strong_trace.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    apply eLpNorm_congr_ae
    exact (hagree t ht).sub Filter.EventuallyEq.rfl
  refine ⟨hrestart, ?_⟩
  intro w H hw
  intro t ht
  by_cases hpos : 0 < t
  · have hcomparison := CRITICAL_LERAY_HOPF_SERRIN_COMPARISON_ON
      ν hν (criticalL2Representative (u δ)) w (timeTranslate ε v) H
      (timeTranslate ε p) hw (positiveSmoothNSE_test hshift)
      (fun r hr => positiveSmoothNSE_pressure_spatial_smooth hshift hr)
      hshift.pressure_periodic hshift.equation htrace t hpos
      (positive_reference_shifted_serrin hε.le hSerrin t hpos)
    exact (hcomparison t ⟨hpos, le_rfl⟩).trans (hagree t hpos).symm
  · have htzero : t = 0 := le_antisymm (le_of_not_gt hpos) ht
    subst t
    exact hw.initial.trans hrestart.initial.symm

theorem LH_UNIQUE_FUTURE_OF_POSITIVE_FLOW
    {ν : ℝ} {a : CriticalPhysicalL2} {u : Velocity} {G : WeakGradientTrajectory}
    (hν : 0 < ν) (hu : CriticalLerayHopf ν a u G)
    (L : CriticalPositiveSobolevFlow ν)
    {s δ : ℝ} (hs : 0 ≤ s) (hδ : s < δ)
    (heq : ∀ r : ℝ, s < r →
      u r =ᵐ[volume.restrict unitCube] L.velocity (r - s))
    (hSerrin : ∀ T : ℝ, 0 < T →
      MemLp (fun t => criticalSpatialNorm 6 (L.velocity t)) 4
        (volume.restrict (Ioc (0 : ℝ) T))) :
    UniqueFuture ν u G δ :=
  LH_UNIQUE_FUTURE_OF_POSITIVE_REFERENCE hν hu (CRITICAL_POSITIVE_PHYSICAL_NSE L)
    hs hδ heq hSerrin

end
end QuasiFeffermanB
