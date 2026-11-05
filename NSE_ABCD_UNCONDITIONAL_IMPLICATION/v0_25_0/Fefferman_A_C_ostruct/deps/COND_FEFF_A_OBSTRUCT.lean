import CondTrace
import CondRecurrence
import CondPoly
import CondGeometry
import CondDecay
import CondSeries
import CondRadial
import CondRadialEval

namespace CondFeffA

open Fefferman Fefferman.ConcreteReal MeasureTheory
open scoped Topology ContDiff

abbrev WitnessAt (c : ℝ) (s : Solution realAnalysis) : Prop :=
  globalSolution realAnalysis .wholeSpace unitViscosity (datum c) (zeroForce realAnalysis) s

abbrev GlobalAt (c : ℝ) : Prop :=
  hasGlobalSolution realAnalysis .wholeSpace unitViscosity (datum c) (zeroForce realAnalysis)

/-- Transfer from the physical profile's iterated Laplacian at the origin
to the signed coefficients of the scalar radial potential. -/
def RadialHeatIdentification : Prop :=
  ∀ n, heatIterate n 0 0 = CondPoly.radialJet n

theorem concrete_radial_heat_identification : RadialHeatIdentification :=
  radial_heat_of_scalar_extraction concrete_scalar_radial_heat_extraction

/-- Every literal witness must have the specified scalar jet at coordinate 0.
This is the PDE/uniqueness input, not a nonexistence premise. -/
def WitnessJetIdentification (δ : ℝ) : Prop :=
  ∀ c ∈ Set.Ioo 0 δ, ∀ s : Solution realAnalysis, WitnessAt c s →
    ∀ n, rightJet (fun t => s.velocity 0 t 0) n = (jetPolynomial n).eval c

/-- The n=0 identification follows from Fefferman clause 03 alone. -/
theorem witness_initial_jet {c : ℝ} {s : Solution realAnalysis} (hs : WitnessAt c s) :
    rightJet (fun t => s.velocity 0 t 0) 0 = (jetPolynomial 0).eval c := by
  have htrace : clause03 realAnalysis (datum c) s := hs.2.2.1
  rw [jetPolynomial_initial]
  simpa [rightJet] using congrFun (htrace 0) (0 : Fin 3)

theorem witness_factorial_bound {c : ℝ} {s : Solution realAnalysis} (hs : WitnessAt c s) :
    FactorialJetBound (fun n => rightJet (fun t => s.velocity 0 t 0) n) := by
  have h06 : clause06 realAnalysis s := hs.2.2.2.1
  have han := h06.1 (0 : Fin 3)
  obtain ⟨M, hM, hj⟩ :=
    rightJet_bound_of_closedHalfSpace (fun x t => s.velocity x t 0) han
  exact factorialJetBound_of_real_bound hM.le hj

theorem radial_growth (n : ℕ) :
    (2 / 3 : ℝ) * ((2*n+3).factorial : ℝ) ≤ |(jetPolynomial n).coeff 1| := by
  rw [jetPolynomial_linear, concrete_radial_heat_identification n, CondPoly.abs_radialJet]
  exact radial_linear_magnitude_lower n

theorem no_witness_of_unbounded_jets {δ c : ℝ} (hc : c ∈ Set.Ioo 0 δ)
    (hPDE : WitnessJetIdentification δ)
    (hbad : ¬ FactorialJetBound (fun n => (jetPolynomial n).eval c)) : ¬ GlobalAt c := by
  rintro ⟨s, hs⟩
  have he : (fun n => rightJet (fun t => s.velocity 0 t 0) n) =
      (fun n => (jetPolynomial n).eval c) := funext (hPDE c hc s hs)
  have hbound := witness_factorial_bound hs
  rw [he] at hbound
  exact hbad hbound

theorem ae_no_global {δ : ℝ} (hδ : 0 < δ) (hPDE : WitnessJetIdentification δ) :
    ∀ᵐ c : ℝ, c ∈ Set.Ioo 0 δ → ¬ GlobalAt c := by
  have hgeom := interpolationNodeBound_of_degree hδ jetPolynomial_degree
  have h := ae_jet_obstruction (positiveMeasureInterpolation_of_nodes hgeom)
    radial_growth
  filter_upwards [h] with c hc
  exact fun hI => no_witness_of_unbounded_jets hI hPDE (hc hI)

/-- At ν=1 an explicit admissible family member refutes both equivalent
v0.25.0 statements. All outstanding analytic inputs occur before the conclusion. -/
theorem COND_FEFF_A_OBSTRUCT (δ : ℝ) (hδ : 0 < δ)
    (hPDE : WitnessJetIdentification δ) :
    (∃ c ∈ Set.Ioo 0 δ, admissibleInitial realAnalysis .wholeSpace (datum c) ∧
      ¬ FactorialJetBound (fun n => (jetPolynomial n).eval c) ∧ ¬ GlobalAt c) ∧
    ¬ WholeSpaceZeroForceGlobalRegularity ∧ ¬ Fefferman.A realAnalysis := by
  have hgeom := interpolationNodeBound_of_degree hδ jetPolynomial_degree
  obtain ⟨c, hc, hbad⟩ := exists_small_obstructing_amplitude hδ
    (positiveMeasureInterpolation_of_nodes hgeom) radial_growth
  have hadm := datum_admissible c
  have hnone := no_witness_of_unbounded_jets hc hPDE hbad
  have hE : ¬ WholeSpaceZeroForceGlobalRegularity :=
    fun h => hnone (h unitViscosity (datum c) hadm)
  exact ⟨⟨c, hc, hadm, hbad, hnone⟩, hE,
    fun h => hE (WHOLESPACE_ZERO_FORCE_GLOBAL_REGULARITY_IFF_A.mpr h)⟩

/-- The whole positive amplitude half-line follows by countable interval exhaustion. -/
theorem ae_positive_no_global
    (hPDE : ∀ δ : ℝ, 0 < δ → WitnessJetIdentification δ) :
    ∀ᵐ c : ℝ, 0 < c → ¬ GlobalAt c := by
  have hI : ∀ᵐ c : ℝ, ∀ n : ℕ, c ∈ Set.Ioo 0 (n+1 : ℝ) → ¬ GlobalAt c := by
    apply ae_all_iff.mpr
    intro n
    have hδ : 0 < (n+1 : ℝ) := by positivity
    exact ae_no_global hδ (hPDE _ hδ)
  filter_upwards [hI] with c hc
  intro hpos
  obtain ⟨n, hn⟩ := exists_nat_gt c
  exact hc n ⟨hpos, by linarith⟩

/-- The C∞ comparison uses the same differential and energy operators,
changing only the two differentiability orders. -/
@[reducible] noncomputable def classicalAnalysis : Analysis := { realAnalysis with
  smoothSpatial := fun g => ContDiff ℝ ∞ g
  smoothClosedHalfSpace := fun g => ContDiffOn ℝ ∞
    (fun z : RSpace × ℝ => g z.1 z.2) {z : RSpace × ℝ | 0 ≤ z.2} }

abbrev ClassicalGlobalAt (c : ℝ) : Prop :=
  hasGlobalSolution classicalAnalysis .wholeSpace
    ⟨(1 : ℝ), by change (0 : ℝ) < 1; norm_num⟩ (datum c) (zeroForce classicalAnalysis)

theorem coexistence_with_classical_solution {δ : ℝ} (hδ : 0 < δ)
    (hPDE : WitnessJetIdentification δ)
    (hsmall : ∀ c ∈ Set.Ioo 0 δ, ClassicalGlobalAt c) :
    ∃ c ∈ Set.Ioo 0 δ, admissibleInitial realAnalysis .wholeSpace (datum c) ∧
      ClassicalGlobalAt c ∧ ¬ GlobalAt c := by
  obtain ⟨c, hc, hadm, _, hnone⟩ := (COND_FEFF_A_OBSTRUCT δ hδ hPDE).1
  exact ⟨c, hc, hadm, hsmall c hc, hnone⟩

end CondFeffA

#print axioms CondFeffA.COND_FEFF_A_OBSTRUCT
#print axioms CondFeffA.ae_no_global
#print axioms CondFeffA.coexistence_with_classical_solution
