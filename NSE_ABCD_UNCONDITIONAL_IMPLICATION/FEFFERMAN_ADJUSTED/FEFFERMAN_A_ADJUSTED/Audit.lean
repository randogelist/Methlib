import ZeroSeed

set_option autoImplicit false

open Fefferman Fefferman.ConcreteReal Fefferman.ConcreteReal.AdjustedA

/- These examples fix the inspected theorem types independently of their aliases. -/
example (ε : ℝ) : Fefferman_adjusted_A ε := FEF_A_POSITIVE_TIME ε

example (ε : ℝ) (ν : PositiveViscosity realAnalysis) (u₀ : RInitial)
    (ha : admissibleInitial realAnalysis .wholeSpace u₀) (h : PositiveTimeState ε ν u₀) :
    hasGlobalSolution realAnalysis .wholeSpace ν u₀ (zeroForce realAnalysis) :=
  FEF_A_POSITIVE_TIME ε ν u₀ ha h

example (ε : ℝ) (ext : SeedExtension ε) (ν : PositiveViscosity realAnalysis)
    (u₀ : RInitial) (ha : admissibleInitial realAnalysis .wholeSpace u₀)
    (h : FinitePositiveTimeState ε ν u₀) :
    hasGlobalSolution realAnalysis .wholeSpace ν u₀ (zeroForce realAnalysis) :=
  regularity_of_seed_extension ε ext ν u₀ ha h

example (ε : ℝ) (hε : 0 < ε) (ν : PositiveViscosity realAnalysis) :
    admissibleInitial realAnalysis .wholeSpace zeroRInitial ∧
    PositiveTimeState ε ν zeroRInitial ∧
    hasGlobalSolution realAnalysis .wholeSpace ν zeroRInitial (zeroForce realAnalysis) :=
  ⟨ZeroSeed.admissible_zero, zero_is_positive_time_state ε hε ν,
    FEF_A_POSITIVE_TIME ε ν zeroRInitial ZeroSeed.admissible_zero
      (zero_is_positive_time_state ε hε ν)⟩

#print axioms Fefferman.ConcreteReal.AdjustedA.smoothClosedHalfSpaceReal_shift
#print axioms Fefferman.ConcreteReal.shift_clause01
#print axioms Fefferman.ConcreteReal.shift_clause02
#print axioms Fefferman.ConcreteReal.shift_clause03
#print axioms Fefferman.ConcreteReal.shift_clause07
#print axioms Fefferman.ConcreteReal.AdjustedA.shifted_global_solution
#print axioms Fefferman.ConcreteReal.AdjustedA.FEF_A_POSITIVE_TIME
#print axioms Fefferman.ConcreteReal.AdjustedA.regularity_of_seed_extension
#print axioms Fefferman.ConcreteReal.AdjustedA.ZeroSeed.admissible_zero
#print axioms Fefferman.ConcreteReal.AdjustedA.ZeroSeed.zero_small
#print axioms Fefferman.ConcreteReal.AdjustedA.ZeroSeed.zero_global
#print axioms Fefferman.ConcreteReal.AdjustedA.zero_is_positive_time_state
