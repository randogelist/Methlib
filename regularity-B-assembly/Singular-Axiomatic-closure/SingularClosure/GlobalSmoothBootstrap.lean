import SingularClosure.GlobalStrongLimit
import SingularClosure.FourierSobolevRhs
import SingularClosure.SobolevScaleTimeSmooth
import SingularClosure.SobolevSpacetimeSmooth
import SingularClosure.PhysicalTimeDerivative
import SingularClosure.PeriodicFourierInjective

/-! Frozen endpoint 9: actual joint smoothness of the constructed strong limit. -/

set_option autoImplicit false
set_option Elab.async true

open Set
open scoped ContDiff

namespace SingularClosure

noncomputable section

theorem GlobalGalerkinStrongLimit.rhs_eq_sobolevRhs
    {ν : ℝ} {a : Field} {ha : SmoothSigmaZero a} (L : GlobalGalerkinStrongLimit ν a ha)
    (r : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    L.rhs r t = fourierSobolevRhs ν r (L.state (r + 2) t) := by
  have hlower : torusSobolevLower 0 (r + 2) (Nat.zero_le _) (L.state (r + 2) t) =
      L.state 0 t := by
    apply Subtype.ext
    rw [torusSobolevLower_coeff]
    exact L.state_coeff_eq_zero (r + 2) t ht
  apply Subtype.ext
  rw [L.rhs_coeff r t ht, fourierSobolevRhs_coefficient_eq_fullRhs, hlower]

theorem GlobalGalerkinStrongLimit.state_time_smooth
    {ν : ℝ} {a : Field} {ha : SmoothSigmaZero a} (L : GlobalGalerkinStrongLimit ν a ha) :
    ∀ r : ℕ, ContDiffOn ℝ ∞ (L.state r) (Ici 0) := by
  apply SOBOLEV_SCALE_TIME_SMOOTH L.state (fourierSobolevRhs ν)
    L.state_continuous (fourierSobolevRhs_contDiff ν)
  intro r t ht
  rw [← L.rhs_eq_sobolevRhs r t ht]
  exact L.state_derivative r t ht

/-- The actual Galerkin strong limit is smooth on closed forward spacetime. -/
theorem GLOBAL_STRONG_SMOOTH_BOOTSTRAP
    {ν : ℝ} {a : Field} {ha : SmoothSigmaZero a} (L : GlobalGalerkinStrongLimit ν a ha) :
    ContDiffOn ℝ ∞ (fun z : ℝ × Vec => L.velocity z.1 z.2) forwardSpacetime :=
  SOBOLEV_CURVES_JOINT_SPACETIME_SMOOTH L.state L.state_time_smooth L.state_coeff_eq_zero

theorem GlobalGalerkinStrongLimit.velocity_timeDerivative
    {ν : ℝ} {a : Field} {ha : SmoothSigmaZero a} (L : GlobalGalerkinStrongLimit ν a ha)
    (t : ℝ) (ht : 0 ≤ t) :
    timeDerivative L.velocity t = smoothFourierSynthesis (fullFourierRhs ν (L.state 0 t)) := by
  have h := physicalTimeDerivative_of_H4_curve
    (L.state 0) (L.state 4) (L.rhs 0) (L.rhs 4)
    (L.state_coeff_eq_zero 4) (L.rhs_coeff_eq_zero 4) (L.state_derivative 4) t ht
  rw [L.rhs_coeff 0 t ht] at h
  exact h

end

end SingularClosure
