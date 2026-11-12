import SingularClosure.CriticalPositiveTimeSmooth
import SingularClosure.CriticalPositivePhysical
import SingularClosure.PhysicalNSEIdentity
import SingularClosure.PeriodicFourierInjective
import SingularClosure.FourierSobolevRhs

/-! Actual positive-time Sobolev flows and their literal physical NSE realization.
This is an auxiliary construction; existence is a separate theorem. -/
set_option autoImplicit false
set_option Elab.async true
open Set
open scoped ContDiff
namespace SingularClosure
noncomputable section

/-- A compatible actual Sobolev scale satisfying the actual unforced NSE RHS. -/
structure CriticalPositiveSobolevFlow (ν : ℝ) where
  state : ∀ r : ℕ, ℝ → TorusSobolev r
  continuous : ∀ r : ℕ, ContinuousOn (state r) (Ioi 0)
  coeff : ∀ (r : ℕ) (t : ℝ), 0 < t → (state r t).val = (state 0 t).val
  derivative : ∀ (r : ℕ) (t : ℝ), 0 < t →
    HasDerivWithinAt (state r) (fourierSobolevRhs ν r (state (r + 2) t)) (Ioi 0) t
  reality : ∀ t : ℝ, 0 < t → SpectralReality (state 0 t).val
  solenoidal : ∀ t : ℝ, 0 < t → SpectralSolenoidal (state 0 t).val
  mean_zero : ∀ t : ℝ, 0 < t → SpectralMeanZero (state 0 t).val

def CriticalPositiveSobolevFlow.velocity {ν : ℝ} (L : CriticalPositiveSobolevFlow ν) :
    Velocity := fun t => smoothFourierSynthesis (L.state 0 t).val

def CriticalPositiveSobolevFlow.pressure {ν : ℝ} (L : CriticalPositiveSobolevFlow ν) :
    Pressure := fun t => fullTransportPressure (L.state 0 t)

theorem CriticalPositiveSobolevFlow.state_all_mem
    {ν : ℝ} (L : CriticalPositiveSobolevFlow ν) (t : ℝ) (ht : 0 < t) (s : ℕ) :
    Memℓp (sobolevWeightedCoeff s (L.state 0 t).val) 2 := by
  rw [← L.coeff s t ht]
  exact (L.state s t).property

theorem CriticalPositiveSobolevFlow.rhs_coeff
    {ν : ℝ} (L : CriticalPositiveSobolevFlow ν) (r : ℕ) (t : ℝ) (ht : 0 < t) :
    (fourierSobolevRhs ν r (L.state (r + 2) t)).val = fullFourierRhs ν (L.state 0 t) := by
  have hlower : torusSobolevLower 0 (r + 2) (Nat.zero_le _) (L.state (r + 2) t) =
      L.state 0 t := by
    apply Subtype.ext
    rw [torusSobolevLower_coeff]
    exact L.coeff (r + 2) t ht
  rw [fourierSobolevRhs_coefficient_eq_fullRhs, hlower]

theorem CriticalPositiveSobolevFlow.time_smooth
    {ν : ℝ} (L : CriticalPositiveSobolevFlow ν) :
    ∀ r : ℕ, ContDiffOn ℝ ∞ (L.state r) (Ioi 0) :=
  CRITICAL_POSITIVE_SCALE_TIME_SMOOTH L.state (fourierSobolevRhs ν)
    L.continuous (fourierSobolevRhs_contDiff ν) L.derivative

theorem CriticalPositiveSobolevFlow.velocity_spacetime_smooth
    {ν : ℝ} (L : CriticalPositiveSobolevFlow ν) :
    ContDiffOn ℝ ∞ (fun z : ℝ × Vec => L.velocity z.1 z.2) positiveSpacetime :=
  CRITICAL_POSITIVE_JOINT_SPACETIME_SMOOTH L.state L.time_smooth L.coeff

theorem CriticalPositiveSobolevFlow.pressure_spacetime_smooth
    {ν : ℝ} (L : CriticalPositiveSobolevFlow ν) :
    ContDiffOn ℝ ∞ (fun z : ℝ × Vec => L.pressure z.1 z.2) positiveSpacetime :=
  CRITICAL_POSITIVE_PRESSURE_JOINT_SMOOTH L.state L.time_smooth L.coeff

theorem CriticalPositiveSobolevFlow.velocity_timeDerivative
    {ν : ℝ} (L : CriticalPositiveSobolevFlow ν) (t : ℝ) (ht : 0 < t) :
    timeDerivative L.velocity t = smoothFourierSynthesis (fullFourierRhs ν (L.state 0 t)) := by
  let R : ∀ s : ℕ, ℝ → TorusSobolev s := fun s z =>
    fourierSobolevRhs ν s (L.state (s + 2) z)
  have hr (z : ℝ) (hz : 0 < z) : (R 4 z).val = (R 0 z).val := by
    change (fourierSobolevRhs ν 4 (L.state 6 z)).val =
      (fourierSobolevRhs ν 0 (L.state 2 z)).val
    rw [L.rhs_coeff 4 z hz, L.rhs_coeff 0 z hz]
  have h := CRITICAL_POSITIVE_PHYSICAL_TIME_DERIVATIVE
    (L.state 0) (L.state 4) (R 0) (R 4) (L.coeff 4) hr (L.derivative 4) t ht
  change timeDerivative L.velocity t = smoothFourierSynthesis (R 0 t).val at h
  rw [show (R 0 t).val = fullFourierRhs ν (L.state 0 t) from L.rhs_coeff 0 t ht] at h
  exact h

theorem CriticalPositiveSobolevFlow.physical_equation
    {ν : ℝ} (L : CriticalPositiveSobolevFlow ν) (t : ℝ) (ht : 0 < t) (x : Vec) :
    timeDerivative L.velocity t x + convection (L.velocity t) x +
      gradient (L.pressure t) x = ν • laplacian (L.velocity t) x := by
  have hr (s : ℕ) : Memℓp (sobolevWeightedCoeff s (fullFourierRhs ν (L.state 0 t))) 2 := by
    rw [← L.rhs_coeff s t ht]
    exact (fourierSobolevRhs ν s (L.state (s + 2) t)).property
  rw [L.velocity_timeDerivative t ht]
  exact PHYSICAL_NSE_OF_FULL_FOURIER_RHS ν (L.state 0 t) (L.state_all_mem t ht)
    (L.reality t ht) (L.solenoidal t ht) hr x

theorem CriticalPositiveSobolevFlow.velocity_smoothSigmaZero
    {ν : ℝ} (L : CriticalPositiveSobolevFlow ν) (t : ℝ) (ht : 0 < t) :
    SmoothSigmaZero (L.velocity t) :=
  smoothFourierSynthesis_smoothSigmaZero (L.state 0 t).val (L.state_all_mem t ht)
    (L.mean_zero t ht) (L.solenoidal t ht)

/-- Literal positive-time NSE properties; no initial-time differentiability is asserted. -/
structure PositiveSmoothNSE (ν : ℝ) (u : Velocity) (p : Pressure) : Prop where
  velocity_smooth : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2) positiveSpacetime
  pressure_smooth : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => p z.1 z.2) positiveSpacetime
  velocity_periodic : ∀ t : ℝ, 0 < t → SpatialPeriodic (u t)
  pressure_periodic : ∀ t : ℝ, 0 < t → SpatialPeriodic (p t)
  divergence_free : ∀ t : ℝ, 0 < t → ∀ x : Vec, divergence (u t) x = 0
  equation : ∀ t : ℝ, 0 < t → ∀ x : Vec,
    timeDerivative u t x + convection (u t) x + gradient (p t) x = ν • laplacian (u t) x
  velocity_mean_zero : ∀ t : ℝ, 0 < t → MeanZero (u t)
  pressure_mean_zero : ∀ t : ℝ, 0 < t → PressureMeanZero (p t)

theorem CRITICAL_POSITIVE_PHYSICAL_NSE
    {ν : ℝ} (L : CriticalPositiveSobolevFlow ν) :
    PositiveSmoothNSE ν L.velocity L.pressure := by
  refine {
    velocity_smooth := L.velocity_spacetime_smooth
    pressure_smooth := L.pressure_spacetime_smooth
    velocity_periodic := fun t ht => (L.velocity_smoothSigmaZero t ht).periodic
    pressure_periodic := fun t _ => fullTransportPressure_periodic (L.state 0 t)
    divergence_free := fun t ht => (L.velocity_smoothSigmaZero t ht).divergence_free
    equation := L.physical_equation
    velocity_mean_zero := fun t ht => (L.velocity_smoothSigmaZero t ht).mean_zero
    pressure_mean_zero := ?_
  }
  intro t ht
  exact fullTransportPressure_meanZero (L.state 0 t) (L.state_all_mem t ht)
    (L.reality t ht) (L.solenoidal t ht)

end
end SingularClosure
