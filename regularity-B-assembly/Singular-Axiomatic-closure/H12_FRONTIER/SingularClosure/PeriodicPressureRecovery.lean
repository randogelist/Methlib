import SingularClosure.GlobalSmoothBootstrap
import SingularClosure.PhysicalNSEIdentity
import SingularClosure.SobolevPressure
import SingularClosure.PressureQuadraticCoefficient

/-! Actual smooth normalized pressure and literal periodic NSE recovery. -/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory
open scoped ContDiff BigOperators

namespace SingularClosure

noncomputable section

def GlobalGalerkinStrongLimit.pressure
    {ν : ℝ} {a : Field} {ha : SmoothSigmaZero a} (L : GlobalGalerkinStrongLimit ν a ha) :
    Pressure := fun t => fullTransportPressure (L.state 0 t)

theorem GlobalGalerkinStrongLimit.pressure_spacetime_smooth
    {ν : ℝ} {a : Field} {ha : SmoothSigmaZero a} (L : GlobalGalerkinStrongLimit ν a ha) :
    ContDiffOn ℝ ∞ (fun z : ℝ × Vec => L.pressure z.1 z.2) forwardSpacetime :=
  SOBOLEV_TRANSPORT_PRESSURE_JOINT_SMOOTH L.state L.state_time_smooth L.state_coeff_eq_zero

theorem GlobalGalerkinStrongLimit.physical_equation
    {ν : ℝ} {a : Field} {ha : SmoothSigmaZero a} (L : GlobalGalerkinStrongLimit ν a ha)
    (t : ℝ) (ht : 0 ≤ t) (x : Vec) :
    timeDerivative L.velocity t x + convection (L.velocity t) x +
      gradient (L.pressure t) x = ν • laplacian (L.velocity t) x := by
  have hr (s : ℕ) : Memℓp (sobolevWeightedCoeff s (fullFourierRhs ν (L.state 0 t))) 2 := by
    rw [← L.rhs_coeff s t ht]
    exact (L.rhs s t).property
  rw [L.velocity_timeDerivative t ht]
  exact PHYSICAL_NSE_OF_FULL_FOURIER_RHS ν (L.state 0 t) (L.state_all_mem t ht)
    (L.reality 0 t ht) (L.solenoidal 0 t ht) hr x

theorem GlobalGalerkinStrongLimit.globalSmoothNSE
    {ν : ℝ} {a : Field} {ha : SmoothSigmaZero a} (L : GlobalGalerkinStrongLimit ν a ha) :
    GlobalSmoothNSE ν a L.velocity L.pressure := by
  refine {
    velocity_smooth := GLOBAL_STRONG_SMOOTH_BOOTSTRAP L
    pressure_smooth := L.pressure_spacetime_smooth
    velocity_periodic := fun t ht => (L.velocity_smoothSigmaZero t ht).periodic
    pressure_periodic := fun t _ => fullTransportPressure_periodic (L.state 0 t)
    divergence_free := fun t ht => (L.velocity_smoothSigmaZero t ht).divergence_free
    equation := L.physical_equation
    initial := L.velocity_initial
    velocity_mean_zero := fun t ht => (L.velocity_smoothSigmaZero t ht).mean_zero
    pressure_mean_zero := ?_
  }
  intro t ht
  exact fullTransportPressure_meanZero (L.state 0 t) (L.state_all_mem t ht)
    (L.reality 0 t ht) (L.solenoidal 0 t ht)

/-- Frozen endpoint 10: literal smooth NSE and the exact normalized quadratic
pressure coefficients. -/
theorem PERIODIC_PRESSURE_RECOVERY
    {ν : ℝ} {a : Field} {ha : SmoothSigmaZero a} (L : GlobalGalerkinStrongLimit ν a ha) :
    GlobalSmoothNSE ν a L.velocity L.pressure ∧
      ∀ t : ℝ, 0 ≤ t → ∀ k : Frequency,
        (∫ x in unitCube, star (fourierCharacter k x) * (L.pressure t x : ℂ)) =
          if k = 0 then 0 else
            -(∑ i : Fin 3, ∑ j : Fin 3, (k i : ℂ) * (k j : ℂ) *
              (∑' p : Frequency, (L.state 0 t).val p i * (L.state 0 t).val (k - p) j)) /
                (∑ i : Fin 3, (k i : ℂ) ^ 2) := by
  refine ⟨L.globalSmoothNSE, ?_⟩
  intro t ht k
  exact fullTransportPressure_fourierCoeff_quadratic (L.state 0 t)
    (L.state_all_mem t ht) (L.reality 0 t ht) (L.solenoidal 0 t ht) k

end

end SingularClosure
