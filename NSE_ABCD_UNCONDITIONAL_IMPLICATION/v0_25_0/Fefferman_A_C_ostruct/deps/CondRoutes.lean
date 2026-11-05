import COND_FEFF_A_OBSTRUCT
import CondUniqueness
import CondExpansion
import CondRawExpand

namespace CondFeffA
open Fefferman Fefferman.ConcreteReal
open scoped Topology

theorem witnessJetIdentification_of_recurrences {δ : ℝ}
    (hphysical : PhysicalProjectedRecurrence δ) (hexpand : FiniteExpansionLaw δ) :
    WitnessJetIdentification δ := by
  intro c hc s hs n
  have hf := witness_fields_eq_of_recurrences hc s hs hphysical hexpand n
  have hsample := congrFun (congrFun hf (0 : RSpace)) (0 : Fin 3)
  exact hsample.trans (evalField_sample c n)

/-- A local right-hand uniqueness statement and the canonical jet recursion
suffice; no values of the chosen trace at negative times are used. -/
theorem witnessJetIdentification_of_local_trace {δ : ℝ} (trace : ℝ → ℝ → ℝ)
    (hlocal : ∀ c ∈ Set.Ioo 0 δ, ∀ s : Solution realAnalysis, WitnessAt c s →
      (fun t => s.velocity 0 t 0) =ᶠ[𝓝[Set.Ici (0 : ℝ)] 0] trace c)
    (hjets : ∀ c ∈ Set.Ioo 0 δ, ∀ n, rightJet (trace c) n = (jetPolynomial n).eval c) :
    WitnessJetIdentification δ := by
  intro c hc s hs n
  have he : (fun t => s.velocity 0 t 0) =ᶠ[𝓝[insert (0 : ℝ) (Set.Ici 0)] 0] trace c := by
    simpa only [Set.insert_eq_of_mem (Set.self_mem_Ici : (0 : ℝ) ∈ Set.Ici 0)] using
      hlocal c hc s hs
  exact (Filter.EventuallyEq.iteratedDerivWithin_eq_of_nhds_insert n he).trans (hjets c hc n)

theorem endpoint_failure_of_operator_inputs {δ : ℝ} (hδ : 0 < δ)
    (hpressure : PressureGradientIdentification δ)
    (hheat : HeatCoefficientExpansion δ) (hproject : ProjectedCoefficientExpansion δ) :
    ¬ WholeSpaceZeroForceGlobalRegularity ∧ ¬ Fefferman.A realAnalysis :=
  (COND_FEFF_A_OBSTRUCT δ hδ (witnessJetIdentification_of_recurrences
    (projectedRecurrence_of_momentum_pressure
      (differentiatedMomentum_of_higher_raw (concrete_higher_raw_expansion δ)) hpressure)
    (finiteExpansionLaw_of_operator_expansions hheat hproject))).2

/-- Alternative route through a locally constructed canonical physical velocity.
The horizon may depend on amplitude; each use of uniqueness compares the same datum. -/
theorem witnessJetIdentification_of_energy_comparison {δ : ℝ}
    (v : ℝ → RVelocity) (T : ℝ → ℝ)
    (hT : ∀ c ∈ Set.Ioo 0 δ, 0 < T c)
    (hi : ∀ c ∈ Set.Ioo 0 δ, ∀ x, v c x 0 = datum c x)
    (hcont : ∀ c ∈ Set.Ioo 0 δ, ∀ t ∈ Set.Icc 0 (T c), Continuous (fun x => v c x t))
    (hL2 : ∀ c ∈ Set.Ioo 0 δ, ∀ t ∈ Set.Icc 0 (T c), squareIntegrableReal (fun x => v c x t))
    (hest : ∀ c ∈ Set.Ioo 0 δ, ∀ s : Solution realAnalysis, WitnessAt c s →
      LocalDifferenceEstimate s.velocity (v c) (T c))
    (hjets : ∀ c ∈ Set.Ioo 0 δ, ∀ n,
      rightJet (fun t => v c 0 t 0) n = (jetPolynomial n).eval c) : WitnessJetIdentification δ := by
  apply witnessJetIdentification_of_local_trace (fun c t => v c 0 t 0) _ hjets
  intro c hc s hs
  exact witness_local_trace_of_difference_estimate (hT c hc) (v c) hs
    (hi c hc) (hcont c hc) (hL2 c hc) (hest c hc s hs)

theorem endpoint_failure_of_pressure_and_row_operators {δ : ℝ} (hδ : 0 < δ)
    (hpressure : PressureGradientIdentification δ)
    (hheat : HeatRowLinearity δ) (hproject : ProjectedRowBilinearity δ) :
    ¬ WholeSpaceZeroForceGlobalRegularity ∧ ¬ Fefferman.A realAnalysis :=
  endpoint_failure_of_operator_inputs hδ hpressure
    (heatExpansion_of_rowLinearity hheat) (projectedExpansion_of_rowBilinearity hproject)

end CondFeffA
