import SingularClosure.SobolevPressure
import SingularClosure.CriticalPositiveSpacetime

set_option autoImplicit false
set_option Elab.async true

open Set
open scoped ContDiff

namespace SingularClosure
noncomputable section

theorem critical_positivePressureCurve_contDiffOn
    (U : ∀ s : ℕ, ℝ → TorusSobolev s)
    (hU : ∀ s : ℕ, ContDiffOn ℝ ∞ (U s) (Ioi (0 : ℝ))) (s : ℕ) :
    ContDiffOn ℝ ∞ (sobolevTransportPressureCurve U s) (Ioi (0 : ℝ)) := by
  have hprod : ContDiffOn ℝ ∞
      (fun t => sobolevDivergenceProduct s (U (s + 2) t) (U (s + 2) t)) (Ioi (0 : ℝ)) :=
    (sobolevDivergenceProduct_diagonal_contDiff s).fun_comp_contDiffOn (hU (s + 2))
  exact ((torusSobolevPressure s).restrictScalars ℝ).contDiff.fun_comp_contDiffOn hprod

theorem critical_positivePressureCurve_coeff
    (U : ∀ s : ℕ, ℝ → TorusSobolev s)
    (hcoeff : ∀ (s : ℕ) (t : ℝ), 0 < t → (U s t).val = (U 0 t).val)
    (s : ℕ) (t : ℝ) (ht : 0 < t) :
    (sobolevTransportPressureCurve U s t).val =
      pressureVectorCoeff (fullTransportCoefficients (U 0 t)) := by
  have hlower : torusSobolevLower 0 (s + 2) (Nat.zero_le _) (U (s + 2) t) = U 0 t := by
    apply Subtype.ext
    simpa only [torusSobolevLower_coeff] using hcoeff (s + 2) t ht
  rw [sobolevTransportPressureCurve, torusSobolevPressure_coeff, sobolevDivergenceProduct_coeff]
  apply congrArg pressureVectorCoeff
  funext k i
  unfold sobolevDivergenceProductCoeff fullTransportCoefficients
  simp only [hlower]

/-- The actual pressure of the actual infinite transport is jointly smooth
on strictly positive spacetime. -/
theorem CRITICAL_POSITIVE_PRESSURE_JOINT_SMOOTH
    (U : ∀ s : ℕ, ℝ → TorusSobolev s)
    (hU : ∀ s : ℕ, ContDiffOn ℝ ∞ (U s) (Ioi (0 : ℝ)))
    (hcoeff : ∀ (s : ℕ) (t : ℝ), 0 < t → (U s t).val = (U 0 t).val) :
    ContDiffOn ℝ ∞
      (fun z : ℝ × Vec => fullTransportPressure (U 0 z.1) z.2) positiveSpacetime := by
  have hP : ∀ (s : ℕ) (t : ℝ), 0 < t →
      (sobolevTransportPressureCurve U s t).val = (sobolevTransportPressureCurve U 0 t).val := by
    intro s t ht
    rw [critical_positivePressureCurve_coeff U hcoeff s t ht,
      critical_positivePressureCurve_coeff U hcoeff 0 t ht]
  have hjoint := CRITICAL_POSITIVE_JOINT_SPACETIME_SMOOTH
    (sobolevTransportPressureCurve U) (critical_positivePressureCurve_contDiffOn U hU) hP
  have hscalar := (EuclideanSpace.proj (0 : Fin 3) : Vec →L[ℝ] ℝ).contDiff.fun_comp_contDiffOn hjoint
  apply hscalar.congr
  intro z hz
  change fullTransportPressure (U 0 z.1) z.2 =
    smoothFourierSynthesis (sobolevTransportPressureCurve U 0 z.1).val z.2 0
  rw [critical_positivePressureCurve_coeff U hcoeff 0 z.1 hz,
    smoothFourierSynthesis_pressureVector_first]
  rfl

end

end SingularClosure
