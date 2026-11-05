import CondEvolution

namespace CondFeffA
open Fefferman Fefferman.ConcreteReal

abbrev IsWitness (c : ℝ) (s : Solution realAnalysis) : Prop :=
  globalSolution realAnalysis .wholeSpace unitViscosity (datum c) (zeroForce realAnalysis) s

noncomputable def pressureJet (s : Solution realAnalysis) (n : ℕ) (x : RSpace) : ℝ :=
  rightJet (fun t => s.pressure x t) n

/-- Right differentiation of the *unprojected* momentum equation at t=0.
The pressure is the pressure of the same witness. -/
def DifferentiatedMomentum (δ : ℝ) : Prop :=
  ∀ c ∈ Set.Ioo 0 δ, ∀ s : Solution realAnalysis, IsWitness c s → ∀ (n : ℕ) (x : RSpace) (i : Fin 3),
    timeJetField s (n+1) x i = heatStep (timeJetField s n) x i -
      (∑ j ∈ Finset.range (n+1), (n.choose j : ℝ) *
        transport (timeJetField s j) (timeJetField s (n-j)) x i) -
      spatialDerivative i (pressureJet s n) x

/-- Whole-space Newton potential for the physical pressure gradient on the
differentiated transport terms. This includes the removal of any harmonic
pressure-gradient ambiguity. No pressure value is normalized. -/
def PressureGradientIdentification (δ : ℝ) : Prop :=
  ∀ c ∈ Set.Ioo 0 δ, ∀ s : Solution realAnalysis, IsWitness c s → ∀ (n : ℕ) (x : RSpace) (i : Fin 3),
    spatialDerivative i (pressureJet s n) x =
      ∑ j ∈ Finset.range (n+1), (n.choose j : ℝ) *
        spatialDerivative i (newtonPotential
          (fieldDiv (transport (timeJetField s j) (timeJetField s (n-j))))) x

theorem projectedRecurrence_of_momentum_pressure {δ : ℝ}
    (hmomentum : DifferentiatedMomentum δ) (hpressure : PressureGradientIdentification δ) :
    PhysicalProjectedRecurrence δ := by
  intro c hc s hs n
  funext x i
  rw [hmomentum c hc s hs n x i, hpressure c hc s hs n x i]
  simp only [nextTimeJet, projectedTransport, mul_add, Finset.sum_add_distrib]
  ring

end CondFeffA
