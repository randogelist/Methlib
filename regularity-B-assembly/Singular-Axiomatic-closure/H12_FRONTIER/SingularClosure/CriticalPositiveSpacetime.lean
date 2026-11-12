import SingularClosure.SobolevSpacetimeSmooth

/-! Joint spacetime smoothness of the actual Fourier synthesis. Each finite
spacetime order is obtained by evaluating its corresponding higher Sobolev
curve through the proved spatially smooth operator-valued Fourier series. -/

set_option autoImplicit false
set_option Elab.async true

open Set
open scoped ContDiff

namespace SingularClosure

noncomputable section

/-- Strictly positive spacetime; no initial-time smoothness is asserted. -/
def positiveSpacetime : Set (ℝ × Vec) := {z | 0 < z.1}


theorem critical_positiveCurve_spacetime_contDiffOn_nat (n : ℕ)
    (U : ℝ → TorusSobolev (n + 4)) (hU : ContDiffOn ℝ n U (Ioi (0 : ℝ))) :
    ContDiffOn ℝ n
      (fun z : ℝ × Vec => smoothFourierSynthesis (U z.1).val z.2) positiveSpacetime := by
  have hE : ContDiffOn ℝ n
      (fun z : ℝ × Vec => sobolevPhysicalEvaluation n z.2) positiveSpacetime :=
    ((sobolevPhysicalEvaluation_contDiff n).comp contDiff_snd).contDiffOn
  have htime : ContDiffOn ℝ n (fun z : ℝ × Vec => U z.1) positiveSpacetime :=
    hU.comp contDiff_fst.contDiffOn (fun z hz => hz)
  simpa only [sobolevPhysicalEvaluation_apply] using hE.clm_apply htime

/-- A compatible family of actual smooth Sobolev trajectories synthesizes an
actual jointly smooth velocity, on strictly positive times. -/
theorem CRITICAL_POSITIVE_JOINT_SPACETIME_SMOOTH
    (U : ∀ s : ℕ, ℝ → TorusSobolev s)
    (hU : ∀ s : ℕ, ContDiffOn ℝ ∞ (U s) (Ioi (0 : ℝ)))
    (hcoeff : ∀ (s : ℕ) (t : ℝ), 0 < t → (U s t).val = (U 0 t).val) :
    ContDiffOn ℝ ∞
      (fun z : ℝ × Vec => smoothFourierSynthesis (U 0 z.1).val z.2) positiveSpacetime := by
  apply contDiffOn_infty.mpr
  intro n
  have h := critical_positiveCurve_spacetime_contDiffOn_nat n (U (n + 4))
    ((contDiffOn_infty.mp (hU (n + 4))) n)
  apply h.congr
  intro z hz
  exact congrArg (fun c : FourierCoeff => smoothFourierSynthesis c z.2)
    (hcoeff (n + 4) z.1 hz).symm

end

end SingularClosure
