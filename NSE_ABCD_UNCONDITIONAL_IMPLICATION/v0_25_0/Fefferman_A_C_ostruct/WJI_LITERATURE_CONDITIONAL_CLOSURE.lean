import WITNESS_JET_IDENTIFICATION_ONE
import WJILocalSlab

/-!
Literature-conditional assembly for the literal v0.25.0 analytic endpoint.

The proposition below is an EXPLICIT HYPOTHESIS. It is the derived regularity
corollary attributed to Tao, Analysis & PDE 6 (2013), Corollaries 11.1 and 4.3,
Theorem 5.4(iv), followed by Sobolev embedding. These literature results and
their Sobolev adapter are NOT proved or imported as proved theorems here.

No new axiom is declared. The conclusion concerns `realAnalysis`, whose
witnesses are analytic at the initial face. It does not refute the classical
C-infinity formulation of Fefferman A.
-/

namespace CondFeffA.Literature

open Fefferman Fefferman.ConcreteReal MeasureTheory Filter Set
open CondFeffA.WJISlab
open scoped ENNReal Topology

noncomputable section

/-- The sole literature admission: every smooth finite-energy slab with the
specified Schwartz initial datum has finite mixed-derivative bounds up to the
initial face. For each time order and finite spatial order, one bound works
for every coordinate and spatial word of at most that order. The norms concern
ordinary derivatives at positive times, with no jet-polynomial premise. -/
def LiteratureSchwartzSlabRegularity : Prop :=
  ∀ (c : ℝ) (s : Solution realAnalysis) (T : ℝ), 0 < T →
    SmoothFiniteEnergySlab c T s →
    (∀ i : Fin 3, SchwartzRepresentative (fun x => datum c x i)) →
    ∀ (n k : ℕ), ∃ C : ENNReal, C < ⊤ ∧
      ∀ (i : Fin 3) (w : List (Fin 3)), w.length ≤ k →
        ∀ᵐ t : ℝ, t ∈ Ioo 0 T →
          eLpNorm (wjiPositiveTimeWord s n i w t) 2 volume +
            eLpNorm (wjiPositiveTimeWord s n i w t) ⊤ volume ≤ C

/-- The published regularity corollary, when admitted with this precise type,
supplies the already implemented positive-time word-bound interface. -/
theorem positive_time_word_bounds
    (hLiterature : LiteratureSchwartzSlabRegularity) :
    WJIPositiveTimeWordBounds 1 := by
  intro c hc s hs n i w
  obtain ⟨C, hC, hbound⟩ := hLiterature c s 1 zero_lt_one
    (witness_finite_slab hs 1) (datum_schwartz c) n w.length
  refine ⟨1, zero_lt_one, C, C, hC, hC, ?_⟩
  filter_upwards [hbound i w le_rfl] with t ht
  intro htime
  have hsum := ht htime
  constructor
  · exact le_self_add.trans hsum
  · exact (self_le_add_left _ _).trans hsum

theorem witness_jet_identification
    (hLiterature : LiteratureSchwartzSlabRegularity) :
    WitnessJetIdentification 1 :=
  wji_one_of_positive_time_bounds (positive_time_word_bounds hLiterature)

/-- Exact root. The literature premise remains an argument of the theorem. -/
theorem WJI_LITERATURE_CONDITIONAL_CLOSURE
    (hLiterature : LiteratureSchwartzSlabRegularity) :
    (∃ c ∈ Ioo (0 : ℝ) 1,
      admissibleInitial realAnalysis .wholeSpace (datum c) ∧
      ¬ FactorialJetBound (fun n => (jetPolynomial n).eval c) ∧ ¬ GlobalAt c) ∧
    ¬ WholeSpaceZeroForceGlobalRegularity ∧ ¬ Fefferman.A realAnalysis :=
  COND_FEFF_A_OBSTRUCT 1 zero_lt_one (witness_jet_identification hLiterature)

theorem analytic_endpoint
    (hLiterature : LiteratureSchwartzSlabRegularity) :
    ¬ WholeSpaceZeroForceGlobalRegularity ∧ ¬ Fefferman.A realAnalysis :=
  (WJI_LITERATURE_CONDITIONAL_CLOSURE hLiterature).2

theorem ae_no_global
    (hLiterature : LiteratureSchwartzSlabRegularity) :
    ∀ᵐ c : ℝ, c ∈ Ioo (0 : ℝ) 1 → ¬ GlobalAt c :=
  CondFeffA.ae_no_global zero_lt_one (witness_jet_identification hLiterature)

end
end CondFeffA.Literature

#print CondFeffA.Literature.LiteratureSchwartzSlabRegularity
#check CondFeffA.Literature.WJI_LITERATURE_CONDITIONAL_CLOSURE
#print axioms CondFeffA.Literature.positive_time_word_bounds
#print axioms CondFeffA.Literature.witness_jet_identification
#print axioms CondFeffA.Literature.WJI_LITERATURE_CONDITIONAL_CLOSURE
#print axioms CondFeffA.Literature.analytic_endpoint
#print axioms CondFeffA.Literature.ae_no_global
