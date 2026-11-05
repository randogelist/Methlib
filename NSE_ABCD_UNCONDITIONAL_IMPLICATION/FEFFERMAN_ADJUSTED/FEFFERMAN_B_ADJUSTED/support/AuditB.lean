import FEF_B_POSITIVE_TIME

set_option autoImplicit false

open Fefferman Fefferman.ConcreteReal Fefferman.ConcreteReal.AdjustedB

/- These examples fix the inspected theorem types independently of their aliases. -/
example (ε : ℝ) : Fefferman_adjusted_B ε := FEF_B_POSITIVE_TIME ε

example (ε : ℝ) (ν : PositiveViscosity realAnalysis) (u₀ : RInitial)
    (ha : admissibleInitial realAnalysis .periodic u₀) (h : PositiveTimeState ε ν u₀) :
    hasGlobalSolution realAnalysis .periodic ν u₀ (zeroForce realAnalysis) :=
  FEF_B_POSITIVE_TIME ε ν u₀ ha h

example (ε : ℝ) (ext : SeedExtension ε) (ν : PositiveViscosity realAnalysis)
    (u₀ : RInitial) (ha : admissibleInitial realAnalysis .periodic u₀)
    (h : FinitePositiveTimeState ε ν u₀) :
    hasGlobalSolution realAnalysis .periodic ν u₀ (zeroForce realAnalysis) :=
  regularity_of_seed_extension ε ext ν u₀ ha h

example (ε : ℝ) (hε : 0 < ε) (ν : PositiveViscosity realAnalysis) :
    admissibleInitial realAnalysis .periodic zeroRInitial ∧
    PositiveTimeState ε ν zeroRInitial ∧
    hasGlobalSolution realAnalysis .periodic ν zeroRInitial (zeroForce realAnalysis) :=
  ⟨ZeroSeed.admissible_zero, zero_is_positive_time_state ε hε ν,
    FEF_B_POSITIVE_TIME ε ν zeroRInitial ZeroSeed.admissible_zero
      (zero_is_positive_time_state ε hε ν)⟩

example (ε : ℝ) (hε : 0 < ε) (ν : PositiveViscosity realAnalysis) :
    ∃ u₀ : RInitial, u₀ ≠ zeroRInitial ∧ admissibleInitial realAnalysis .periodic u₀ ∧
      PositiveTimeState ε ν u₀ ∧
      hasGlobalSolution realAnalysis .periodic ν u₀ (zeroForce realAnalysis) :=
  ConstantSeed.exists_nonzero_positive_time_state ε hε ν

#print axioms Fefferman.ConcreteReal.AdjustedA.smoothClosedHalfSpaceReal_shift
#print axioms Fefferman.ConcreteReal.shift_clause01
#print axioms Fefferman.ConcreteReal.shift_clause02
#print axioms Fefferman.ConcreteReal.shift_clause03
#print axioms Fefferman.ConcreteReal.AdjustedB.shift_clause10
#print axioms Fefferman.ConcreteReal.AdjustedB.shift_periodic_pressure
#print axioms Fefferman.ConcreteReal.AdjustedB.shifted_global_solution
#print axioms Fefferman.ConcreteReal.AdjustedB.FEF_B_POSITIVE_TIME
#print axioms Fefferman.ConcreteReal.AdjustedB.regularity_of_seed_extension
#print axioms Fefferman.ConcreteReal.AdjustedB.ZeroSeed.admissible_zero
#print axioms Fefferman.ConcreteReal.AdjustedB.ZeroSeed.zero_small
#print axioms Fefferman.ConcreteReal.AdjustedB.ZeroSeed.zero_global
#print axioms Fefferman.ConcreteReal.AdjustedB.ZeroSeed.zero_hasGlobalSolution
#print axioms Fefferman.ConcreteReal.AdjustedB.ZeroSeed.zero_positive_flow
#print axioms Fefferman.ConcreteReal.AdjustedB.zero_is_positive_time_state
#print axioms Fefferman.ConcreteReal.AdjustedB.ConstantSeed.exists_nonzero_positive_time_state
