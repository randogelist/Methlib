import SingularClosure.CriticalLimitEquation
import SingularClosure.SobolevCoefficientCalculus

/-! A positive-time Hilbert derivative from the proved modal integral
equation and a continuous actual Sobolev representative of its RHS. -/

set_option autoImplicit false
set_option Elab.async true
open Set Filter MeasureTheory
open scoped Topology Interval

namespace SingularClosure
noncomputable section

theorem critical_positive_sobolev_derivative_of_modal_integral
    (ν : ℝ) (u : ℝ → TorusSobolev 0) (hu : ContinuousOn u (Ici 0))
    (heq : ∀ t : ℝ, 0 ≤ t → ∀ k : Frequency, ∀ i : Fin 3,
      (u t).val k i = (u 0).val k i +
        ∫ z in (0 : ℝ)..t, fullFourierRhs ν (u z) k i)
    (s : ℕ) (v R : ℝ → TorusSobolev s)
    (hv : ∀ t : ℝ, 0 < t → (v t).val = (u t).val)
    (hR : ContinuousOn R (Ioi 0))
    (hRc : ∀ t : ℝ, 0 < t → (R t).val = fullFourierRhs ν (u t))
    (t : ℝ) (ht : 0 < t) : HasDerivAt v (R t) t := by
  let r : ℝ := t / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hrt : r < t := by dsimp [r]; linarith
  let R' : ℝ → TorusSobolev s := fun z => R (max z r)
  have hR' : Continuous R' :=
    hR.comp_continuous (continuous_id.max continuous_const)
      (fun z => hr.trans_le (le_max_right z r))
  have hidentity (z : ℝ) (hz : r ≤ z) :
      v z = v r + ∫ w in r..z, R' w := by
    apply Subtype.ext
    funext k i
    change (v z).val k i = (v r).val k i + (∫ w in r..z, R' w).val k i
    rw [hv z (hr.trans_le hz), hv r hr,
      torusSobolevCoeff_intervalIntegral s R' r z (hR'.intervalIntegrable r z) k i]
    have hcoeff : (∫ w in r..z, (R' w).val k i) =
        ∫ w in r..z, fullFourierRhs ν (u w) k i := by
      apply intervalIntegral.integral_congr
      intro w hw
      have hw' : w ∈ Icc r z := by simpa only [uIcc_of_le hz] using hw
      dsimp only [R']
      rw [max_eq_left hw'.1, hRc w (hr.trans_le hw'.1)]
    rw [hcoeff, heq z (hr.le.trans hz) k i, heq r hr.le k i]
    have hc : ContinuousOn (fun w => fullFourierRhs ν (u w) k i) (Ici 0) :=
      (fullFourierRhs_continuous ν k i).comp_continuousOn hu
    have hi0 : IntervalIntegrable (fun w => fullFourierRhs ν (u w) k i) volume 0 r :=
      (hc.mono (fun w hw => hw.1)).intervalIntegrable_of_Icc hr.le
    have hi1 : IntervalIntegrable (fun w => fullFourierRhs ν (u w) k i) volume r z :=
      (hc.mono (fun w hw => hr.le.trans hw.1)).intervalIntegrable_of_Icc hz
    rw [← intervalIntegral.integral_add_adjacent_intervals hi0 hi1]
    ring
  have hd : HasDerivAt (fun z => v r + ∫ w in r..z, R' w) (R' t) t :=
    ((hR'.integral_hasStrictDerivAt r t).hasDerivAt.const_add (v r))
  have hident : v =ᶠ[𝓝 t] (fun z => v r + ∫ w in r..z, R' w) := by
    filter_upwards [Ioi_mem_nhds hrt] with z hz
    exact hidentity z hz.le
  have h := hd.congr_of_eventuallyEq hident
  simpa only [R', max_eq_left hrt.le] using h

end
end SingularClosure
