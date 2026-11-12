import QuasiFeffermanB.GoodTime
import QuasiFeffermanB.MeanPreservation
import QuasiFeffermanB.RegularReference
import QuasiFeffermanB.CaloricAdmission
import QuasiFeffermanB.SafeCutoff
import QuasiFeffermanB.TailEnergy
import QuasiFeffermanB.TailUniqueness

/-! Deterministic composition over two explicitly named remaining analytic
endpoints. This conditional theorem is not the unconditional frozen root.
-/
set_option autoImplicit false
set_option Elab.async true

open Set Filter MeasureTheory
open scoped ContDiff ENNReal Topology Interval

namespace QuasiFeffermanB
open SingularClosure
noncomputable section

theorem TAIL_REFERENCE_FROM_EXACT_ADMISSION
    {ν : ℝ} (hν : 0 < ν) (hadmit : ExactH1Admission ν)
    {a : CriticalPhysicalL2} (ha : EnergySigmaZero a)
    {u : Velocity} {G : WeakGradientTrajectory}
    (hu : CriticalLerayHopf ν a u G)
    {δ : ℝ} (hδ : cutoff a ν < δ) :
    ∃ (s : ℝ) (L : CriticalPositiveSobolevFlow ν),
      0 < s ∧ s < δ ∧
      ∀ r : ℝ, s < r → u r =ᵐ[volume.restrict unitCube] L.velocity (r - s) := by
  let Good : ℝ → Prop := fun s =>
    CriticalPhysicalH1 (u s) (G s) ∧
      CriticalLerayHopf ν (criticalL2Representative (u s))
        (timeTranslate s u) (timeTranslate s G)
  have hgood : ∀ᵐ s ∂criticalTimeMeasure δ, Good s := by
    simpa only [criticalTimeMeasure, Good] using LH_RESTART_AE_Ioo hu hν.le δ
  obtain ⟨s, hs0, hsδ, hsGood, hsH1, hsmall⟩ :=
    LH_GOOD_SUBCRITICAL_TIME hν hu hδ hgood
  have hσ : EnergySigmaZero (criticalL2Representative (u s)) :=
    LH_POSITIVE_TRACE_ENERGY_SIGMA_ZERO hu ha s hs0
  obtain ⟨R⟩ := hadmit (u s) (G s) hsH1 hσ hsmall
  refine ⟨s, R.flow, hs0, hsδ, ?_⟩
  intro r hr
  have htime : 0 < r - s := sub_pos.mpr hr
  have hcomp := POSITIVE_FLOW_LH_COMPARISON_OF_TRACE_AND_SERRIN
    ν hν (criticalL2Representative (u s)) R.flow R.trace R.serrin
    (timeTranslate s u) (timeTranslate s G) hsGood.2 (r - s) htime
  simpa only [timeTranslate, sub_add_cancel] using hcomp

theorem TAIL_CONCLUSIONS_FROM_EXACT_ADMISSION
    {ν : ℝ} (hν : 0 < ν) (hadmit : ExactH1Admission ν)
    {a : CriticalPhysicalL2} (ha : EnergySigmaZero a)
    {u : Velocity} {G : WeakGradientTrajectory}
    (hu : CriticalLerayHopf ν a u G)
    {δ : ℝ} (hδ : cutoff a ν < δ) :
    HasSmoothTail ν u δ ∧ TailEnergyEquality ν u G δ ∧ UniqueFuture ν u G δ := by
  obtain ⟨s, L, hs0, hsδ, heq⟩ :=
    TAIL_REFERENCE_FROM_EXACT_ADMISSION hν hadmit ha hu hδ
  exact ⟨HAS_SMOOTH_TAIL_OF_POSITIVE_FLOW L s δ hs0.le hsδ heq,
    LH_TAIL_ENERGY_OF_POSITIVE_FLOW hν hu L hs0.le hsδ heq,
    LH_UNIQUE_FUTURE_OF_SMOOTH_FLOW hν hu L hs0.le hsδ heq⟩

theorem Quasi_Fefferman_B_of_analytic_endpoints
    (hexists : ∀ (ν : ℝ), 0 < ν → ∀ (a : CriticalPhysicalL2),
      EnergySigmaZero a →
        ∃ (u : Velocity) (G : WeakGradientTrajectory), CriticalLerayHopf ν a u G)
    (hadmit : ∀ (ν : ℝ), 0 < ν → ExactH1Admission ν) :
    QuasiFeffermanBStatement := by
  intro ν hν a ha
  refine ⟨hexists ν hν a ha, ?_⟩
  intro u G hu
  have htail : ∀ δ : ℝ, cutoff a ν < δ →
      HasSmoothTail ν u δ ∧ TailEnergyEquality ν u G δ ∧ UniqueFuture ν u G δ := by
    intro δ hδ
    exact TAIL_CONCLUSIONS_FROM_EXACT_ADMISSION hν (hadmit ν hν) ha hu hδ
  exact ⟨SAFE_CUTOFF_TAIL hν hu (fun δ hδ => (htail δ hδ).1), htail⟩

end
end QuasiFeffermanB
