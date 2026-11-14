import SingularClosure.PhysicalTimeDerivative
import SingularClosure.CriticalPositivePressure

/-! Literal physical time differentiation on strictly positive times. -/
set_option autoImplicit false
set_option Elab.async true
open Set
namespace SingularClosure
noncomputable section

theorem critical_positiveSynthesis_hasDerivWithinAt_H4
    (u : ℝ → TorusSobolev 4) (r : TorusSobolev 4) (t : ℝ) (x : Vec)
    (hu : HasDerivWithinAt u r (Ioi 0) t) :
    HasDerivWithinAt (fun z => smoothFourierSynthesis (u z).val x)
      (smoothFourierSynthesis r.val x) (Ioi 0) t := by
  have h := (sobolevPhysicalEvaluation4 x).hasFDerivAt.comp_hasDerivWithinAt t hu
  simpa only [Function.comp_def, sobolevPhysicalEvaluation4,
    sobolevPhysicalEvaluation_apply] using! h

/-- No derivative or smoothness at the initial endpoint is required. -/
theorem CRITICAL_POSITIVE_PHYSICAL_TIME_DERIVATIVE
    (u0 : ℝ → TorusSobolev 0) (u4 : ℝ → TorusSobolev 4)
    (r0 : ℝ → TorusSobolev 0) (r4 : ℝ → TorusSobolev 4)
    (hu : ∀ t : ℝ, 0 < t → (u4 t).val = (u0 t).val)
    (hr : ∀ t : ℝ, 0 < t → (r4 t).val = (r0 t).val)
    (hd : ∀ t : ℝ, 0 < t → HasDerivWithinAt u4 (r4 t) (Ioi 0) t)
    (t : ℝ) (ht : 0 < t) :
    timeDerivative (fun z => smoothFourierSynthesis (u0 z).val) t =
      smoothFourierSynthesis (r0 t).val := by
  funext x
  have h := critical_positiveSynthesis_hasDerivWithinAt_H4 u4 (r4 t) t x (hd t ht)
  have h' : HasDerivWithinAt (fun z => smoothFourierSynthesis (u0 z).val x)
      (smoothFourierSynthesis (r4 t).val x) (Ioi 0) t := by
    apply h.congr_of_mem _ ht
    intro z hz
    exact congrArg (fun c : FourierCoeff => smoothFourierSynthesis c x) (hu z hz).symm
  rw [hr t ht] at h'
  exact (h'.hasDerivAt (isOpen_Ioi.mem_nhds ht)).hasDerivWithinAt.derivWithin
    ((uniqueDiffOn_Ici 0) t ht.le)

end
end SingularClosure
