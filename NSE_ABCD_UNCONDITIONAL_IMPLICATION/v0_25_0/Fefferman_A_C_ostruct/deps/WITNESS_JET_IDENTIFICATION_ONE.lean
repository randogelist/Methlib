import WJIHarmonicPressure
import WJINewtonBilinear
import WJINewtonSmooth
import WJINewtonAllOrders
import WJINewtonDistribution
import WJIWordTrace
import CondRoutes

namespace CondFeffA

open Fefferman Fefferman.ConcreteReal
noncomputable section

/-- Analytic reduction of the actual witness jets. The Newton input concerns
all transport sources in the concrete space, independently of any witness. -/
theorem wji_identification_of_velocity_bounds_and_newton {δ : ℝ}
    (hJ : WJIJetsInSobolevSpace δ) (hN : NewtonPoissonOn) :
    WitnessJetIdentification δ := by
  have hpressure := wji_pressure_identification_of_poisson hJ hN
    (wji_newton_scalar_smooth_of_differentiable hN wjiNewtonScalar_differentiable)
  exact witnessJetIdentification_of_recurrences
    (projectedRecurrence_of_momentum_pressure
      (differentiatedMomentum_of_higher_raw (concrete_higher_raw_expansion δ)) hpressure)
    (wji_finiteExpansionLaw_of_newtonPoisson hN wjiNewtonScalar_differentiable δ)

/-- Specialized scope of the candidate. Every remaining premise is explicit. -/
theorem wji_one_of_velocity_bounds_and_newton
    (hJ : WJIJetsInSobolevSpace 1) (hN : NewtonPoissonOn) :
    WitnessJetIdentification 1 :=
  wji_identification_of_velocity_bounds_and_newton hJ hN

theorem wji_endpoint_one_of_velocity_bounds_and_newton
    (hJ : WJIJetsInSobolevSpace 1) (hN : NewtonPoissonOn) :
    ¬WholeSpaceZeroForceGlobalRegularity ∧ ¬Fefferman.A realAnalysis :=
  (COND_FEFF_A_OBSTRUCT 1 zero_lt_one (wji_one_of_velocity_bounds_and_newton hJ hN)).2

/-- Precise external target of this run. Positive-time estimates are stated
for ordinary mixed derivatives, away from the initial-face right-jet conclusion. -/
theorem wji_one_of_positive_time_and_newton
    (hT : WJIPositiveTimeWordBounds 1) (hN : NewtonPoissonOn) :
    WitnessJetIdentification 1 :=
  wji_one_of_velocity_bounds_and_newton
    (wji_jetsInSobolevSpace_of_positive_time_word_bounds hT) hN

theorem wji_analytic_A_false_of_positive_time_and_newton
    (hT : WJIPositiveTimeWordBounds 1) (hN : NewtonPoissonOn) :
    ¬WholeSpaceZeroForceGlobalRegularity ∧ ¬Fefferman.A realAnalysis :=
  (COND_FEFF_A_OBSTRUCT 1 zero_lt_one (wji_one_of_positive_time_and_newton hT hN)).2

/-- Newton's signed Poisson equation and regularity of its gradient on the
actual transport sources. This theorem has no witness or literature premise. -/
theorem wji_newton_poisson_on_sobolev : NewtonPoissonOn :=
  wji_newtonPoisson_of_gradient_mem wji_newton_gradient_regular

/-- The only input is an estimate on ordinary derivatives at positive times. -/
theorem wji_one_of_positive_time_bounds (hT : WJIPositiveTimeWordBounds 1) :
    WitnessJetIdentification 1 :=
  wji_one_of_positive_time_and_newton hT wji_newton_poisson_on_sobolev

theorem wji_analytic_A_false_of_positive_time_bounds (hT : WJIPositiveTimeWordBounds 1) :
    ¬WholeSpaceZeroForceGlobalRegularity ∧ ¬Fefferman.A realAnalysis :=
  (COND_FEFF_A_OBSTRUCT 1 zero_lt_one (wji_one_of_positive_time_bounds hT)).2

end
end CondFeffA

#print axioms CondFeffA.wji_identification_of_velocity_bounds_and_newton
#print axioms CondFeffA.wji_one_of_velocity_bounds_and_newton
#print axioms CondFeffA.wji_endpoint_one_of_velocity_bounds_and_newton

#print axioms CondFeffA.wji_one_of_positive_time_and_newton
#print axioms CondFeffA.wji_analytic_A_false_of_positive_time_and_newton

#print axioms CondFeffA.wji_newton_poisson_on_sobolev
#print axioms CondFeffA.wji_one_of_positive_time_bounds
#print axioms CondFeffA.wji_analytic_A_false_of_positive_time_bounds
