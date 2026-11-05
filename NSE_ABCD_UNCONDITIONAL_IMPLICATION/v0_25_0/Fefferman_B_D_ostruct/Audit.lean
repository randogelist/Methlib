import COND_FEFF_B_OBSTRUCT

open Fefferman Fefferman.ConcreteReal CondFeffB Set

-- Each example checks the exact type even when every proof module was a cache hit.
example : admissibleInitial realAnalysis Domain.periodic shearDatum := shearDatum_admissible
example (ν : PositiveViscosity realAnalysis) :
    ¬ AnalyticWithinAt ℝ (fun t => shearProfile ν.val t 0) (Ici 0) 0 :=
  shearTrace_not_analytic ν.property
example (ν : PositiveViscosity realAnalysis) :
    ¬ hasGlobalSolution realAnalysis Domain.periodic ν shearDatum (zeroForce realAnalysis) :=
  shearDatum_no_periodic_witness ν
example : ¬ PeriodicZeroForceGlobalRegularity := periodic_endpoint_obstruct
example : ¬ Fefferman.B realAnalysis := CondFeffB.COND_FEFF_B_OBSTRUCT

#print axioms Fefferman.ConcreteReal.PERIODIC_ZERO_FORCE_GLOBAL_REGULARITY_IFF_B
#print axioms PeriodicShear.moment_factorial_lower
#print axioms PeriodicShear.moment_no_factorial_bound
#print axioms CondFeffB.shearDatum_admissible
#print axioms CondFeffB.shearProfile_initial
#print axioms CondFeffB.shearVelocity_periodic
#print axioms CondFeffB.shearVelocity_initial
#print axioms CondFeffB.shearProfile_hasDerivAt_space
#print axioms CondFeffB.shearSlope_hasDerivAt_space
#print axioms CondFeffB.shearProfile_hasDerivAt_time
#print axioms CondFeffB.abs_shearSlope_le
#print axioms CondFeffB.analyticRight_normalized_bound
#print axioms CondFeffB.analyticTimeTrace
#print axioms CondFeffB.abs_shearTraceJet_eq_moment
#print axioms CondFeffB.integral_periodic_fluxDivergence
#print axioms CondFeffB.localEnergyBalance
#print axioms CondFeffB.shearProduction_le
#print axioms CondFeffB.fluxDivergence_differenceFlux
#print axioms CondFeffB.cellIntegral_hasDerivAt_pos
#print axioms CondFeffB.origin_eq_of_periodic_energy_ineq
#print axioms CondFeffB.relative_divergence
#print axioms CondFeffB.relative_momentum
#print axioms CondFeffB.candidateFlux_periodic
#print axioms CondFeffB.candidateFlux_regular
#print axioms CondFeffB.candidate_cellEnergy_hasDerivAt
#print axioms CondFeffB.candidate_pointwise_energy_bound
#print axioms CondFeffB.candidate_cellEnergy_differential_bound
#print axioms CondFeffB.candidate_origin_eq_shear
#print axioms CondFeffB.shearTrace_not_analytic
#print axioms CondFeffB.shearDatum_no_periodic_witness
#print axioms CondFeffB.periodic_endpoint_obstruct
#print axioms CondFeffB.COND_FEFF_B_OBSTRUCT
