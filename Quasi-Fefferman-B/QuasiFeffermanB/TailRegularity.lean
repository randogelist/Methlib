import QuasiFeffermanB.RootContract
import SingularClosure.CriticalPositiveFlow

/-! Actual time translation of positive smooth NSE to a closed regular tail. -/
set_option autoImplicit false
set_option Elab.async true

open Set Filter MeasureTheory
open scoped ContDiff ENNReal Topology Interval

namespace QuasiFeffermanB
open SingularClosure
noncomputable section

theorem positive_timeDerivative_translate
    {ν : ℝ} {v : Velocity} {p : Pressure}
    (hv : PositiveSmoothNSE ν v p)
    (s t : ℝ) (ht : 0 < t) (hts : 0 < t - s) (x : Vec) :
    timeDerivative (fun r => v (r - s)) t x = timeDerivative v (t - s) x := by
  have hsmooth : ContDiffOn ℝ ∞ (fun r : ℝ => v r x) (Ioi 0) :=
    hv.velocity_smooth.comp (contDiff_id.prodMk contDiff_const).contDiffOn
      (fun r hr => hr)
  have hdiff : DifferentiableAt ℝ (fun r : ℝ => v r x) (t - s) :=
    (hsmooth.differentiableOn (by simp) (t - s) hts).differentiableAt
      (isOpen_Ioi.mem_nhds hts)
  have hD : HasDerivAt (fun r : ℝ => v r x)
      (timeDerivative v (t - s) x) (t - s) := by
    have heq : timeDerivative v (t - s) x = deriv (fun r : ℝ => v r x) (t - s) :=
      hdiff.hasDerivAt.hasDerivWithinAt.derivWithin
        ((uniqueDiffOn_Ici 0) (t - s) hts.le)
    rw [heq]
    exact hdiff.hasDerivAt
  have hcomp : HasDerivAt (fun r : ℝ => v (r - s) x)
      (timeDerivative v (t - s) x) t := by
    simpa only [Function.comp_def, one_smul] using
      hD.scomp t ((hasDerivAt_id t).sub_const s)
  exact hcomp.hasDerivWithinAt.derivWithin ((uniqueDiffOn_Ici 0) t ht.le)

theorem CLASSICAL_TAIL_OF_POSITIVE_SMOOTH_NSE
    {ν : ℝ} {v : Velocity} {p : Pressure}
    (hv : PositiveSmoothNSE ν v p)
    (s δ : ℝ) (hs : 0 ≤ s) (hsδ : s < δ) :
    ClassicalTail ν δ (fun t => v (t - s)) (fun t => p (t - s)) := by
  have hpositive (t : ℝ) (ht : δ ≤ t) : 0 < t - s := by linarith
  have htime (t : ℝ) (ht : δ ≤ t) : 0 < t := by linarith
  have hmap : MapsTo (fun z : ℝ × Vec => (z.1 - s, z.2))
      (tailSpacetime δ) positiveSpacetime := by
    intro z hz
    change 0 < z.1 - s
    exact hpositive z.1 hz
  have hcont : ContDiff ℝ ∞ (fun z : ℝ × Vec => (z.1 - s, z.2)) :=
    (contDiff_fst.sub contDiff_const).prodMk contDiff_snd
  refine {
    velocity_smooth := hv.velocity_smooth.comp hcont.contDiffOn hmap
    pressure_smooth := hv.pressure_smooth.comp hcont.contDiffOn hmap
    velocity_periodic := fun t ht => hv.velocity_periodic (t - s) (hpositive t ht)
    pressure_periodic := fun t ht => hv.pressure_periodic (t - s) (hpositive t ht)
    divergence_free := fun t ht => hv.divergence_free (t - s) (hpositive t ht)
    equation := ?_
    velocity_mean_zero := fun t ht => hv.velocity_mean_zero (t - s) (hpositive t ht)
    pressure_mean_zero := fun t ht => hv.pressure_mean_zero (t - s) (hpositive t ht)
  }
  intro t ht x
  rw [positive_timeDerivative_translate hv s t (htime t ht) (hpositive t ht) x]
  exact hv.equation (t - s) (hpositive t ht) x

theorem HAS_SMOOTH_TAIL_OF_POSITIVE_REFERENCE
    {ν : ℝ} {u v : Velocity} {p : Pressure}
    (hv : PositiveSmoothNSE ν v p)
    (s δ : ℝ) (hs : 0 ≤ s) (hsδ : s < δ)
    (hagreement : ∀ t : ℝ, s < t →
      u t =ᵐ[volume.restrict unitCube] v (t - s)) :
    HasSmoothTail ν u δ := by
  refine ⟨(fun t => v (t - s)), (fun t => p (t - s)),
    CLASSICAL_TAIL_OF_POSITIVE_SMOOTH_NSE hv s δ hs hsδ, ?_⟩
  intro t ht
  exact hagreement t (hsδ.trans_le ht)

theorem HAS_SMOOTH_TAIL_OF_POSITIVE_FLOW
    {ν : ℝ} {u : Velocity} (L : CriticalPositiveSobolevFlow ν)
    (s δ : ℝ) (hs : 0 ≤ s) (hsδ : s < δ)
    (hagreement : ∀ t : ℝ, s < t →
      u t =ᵐ[volume.restrict unitCube] L.velocity (t - s)) :
    HasSmoothTail ν u δ :=
  HAS_SMOOTH_TAIL_OF_POSITIVE_REFERENCE (CRITICAL_POSITIVE_PHYSICAL_NSE L)
    s δ hs hsδ hagreement

end
end QuasiFeffermanB
