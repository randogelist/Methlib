import QuasiFeffermanB.TailRegularity
import QuasiFeffermanB.ZeroData

/-! Q13: the zero case and the safe closed cutoff, preserving the exact bound. -/
set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory
open scoped ContDiff ENNReal Interval

namespace QuasiFeffermanB
open SingularClosure
noncomputable section

theorem CLASSICAL_TAIL_OF_GLOBAL_SMOOTH_NSE
    {ν : ℝ} {a : Field} {v : Velocity} {p : Pressure}
    (hv : GlobalSmoothNSE ν a v p) (δ : ℝ) (hδ : 0 ≤ δ) :
    ClassicalTail ν δ v p := by
  have htime (t : ℝ) (ht : δ ≤ t) : 0 ≤ t := hδ.trans ht
  have hsubset : tailSpacetime δ ⊆ forwardSpacetime := by
    intro z hz
    exact hδ.trans hz
  exact {
    velocity_smooth := hv.velocity_smooth.mono hsubset
    pressure_smooth := hv.pressure_smooth.mono hsubset
    velocity_periodic := fun t ht => hv.velocity_periodic t (htime t ht)
    pressure_periodic := fun t ht => hv.pressure_periodic t (htime t ht)
    divergence_free := fun t ht => hv.divergence_free t (htime t ht)
    equation := fun t ht => hv.equation t (htime t ht)
    velocity_mean_zero := fun t ht => hv.velocity_mean_zero t (htime t ht)
    pressure_mean_zero := fun t ht => hv.pressure_mean_zero t (htime t ht)
  }

theorem ZERO_LH_HAS_SMOOTH_TAIL
    {ν : ℝ} (hν : 0 ≤ ν) {u : Velocity} {G : WeakGradientTrajectory}
    (hu : CriticalLerayHopf ν (0 : CriticalPhysicalL2) u G)
    (δ : ℝ) (hδ : 0 ≤ δ) : HasSmoothTail ν u δ := by
  obtain ⟨v, p, hv, heq⟩ := ZERO_LH_SMOOTH_REPRESENTATIVE hν hu
  exact ⟨v, p, CLASSICAL_TAIL_OF_GLOBAL_SMOOTH_NSE hv δ hδ,
    fun t ht => heq t (hδ.trans ht)⟩

theorem SAFE_CUTOFF_TAIL
    {ν : ℝ} (hν : 0 < ν) {a : CriticalPhysicalL2}
    {u : Velocity} {G : WeakGradientTrajectory}
    (hu : CriticalLerayHopf ν a u G)
    (hregular : ∀ δ : ℝ, cutoff a ν < δ → HasSmoothTail ν u δ) :
    HasSmoothTail ν u (safeCutoff a ν) := by
  by_cases ha : a = 0
  · subst a
    apply ZERO_LH_HAS_SMOOTH_TAIL hν.le hu
    simp [safeCutoff, cutoff]
  · exact hregular (safeCutoff a ν) (SAFE_CUTOFF_GT a ha hν)

end
end QuasiFeffermanB
