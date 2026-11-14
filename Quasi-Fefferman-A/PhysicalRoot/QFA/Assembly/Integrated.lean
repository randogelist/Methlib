import QFA.Assembly.Chain
import QFA.Assembly.AnalyticChain

/-!
# QFA: analytic absorption to the quantified reference/tail chain

Status: A_TIER_CANDIDATE. Local declarations: LE107--LE108.
External baseline: Lean 4.33.0 and Mathlib
db584cd6d46c92f209a44c0f1c829460d327499d.
No local Lean or Lake execution. Exact external compiler and axiom evidence
are required before promotion.

LC004, LC001 and LC003 imply a universally quantified pointwise absorption
statement for supplied real derivative data. LC002 is derived inside the
analytic chain; it is not an additional independent premise.

The passage from this pointwise statement to an actual subcritical reference
construction is an explicit unresolved input. It requires local strong
evolution, physical nonlinear/derivative identities, a temporal invariant,
and continuation. No inhabitant of that input is supplied here. In particular,
the selected H1 restart is not assumed to carry H2/Laplacian witnesses.

The final implication connects the two branches through that named input.
Domain, Admissible, Reference and Good retain their explicit interpretations
as parameters. No physical smoothness, pressure or QFA root closure follows
without their separate physical realization.
-/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory Filter
open scoped BigOperators BoundedContinuousFunction Topology

namespace QFA.Assembly.Integrated

open QFA.Endpoints.Agmon
open QFA.Endpoints.Representation
open QFA.Assembly.Representation
open QFA.Assembly.Chain
open QFA.Representation

noncomputable section

/-- The exact pointwise consequence used by a future reference-construction
proof. Every field, derivative witness and scalar estimate is quantified
explicitly. This definition does not assert time-dependent H2 realization.
-/
def PointwiseAbsorption (ν : ℝ) : Prop :=
  ∀ (v L : RealL2) (G H : Fin 3 → RealL2) (N d : ℝ),
    CompactDerivativeData v G H L →
    0 ≤ N →
    (∀ V : Space →ᵇ ComplexVector,
      (fun x : Space => V x) =ᵐ[volume] (fun x : Space => complexifyL2 v x) →
        N ≤ ‖V‖ * Real.sqrt (∑ j : Fin 3, ‖G j‖ ^ 2) * Real.sqrt (‖L‖ ^ 2)) →
    (‖v‖ ^ 2) * (∑ j : Fin 3, ‖G j‖ ^ 2) < 4 * Real.pi ^ 2 * ν ^ 4 →
    d / 2 + ν * ‖L‖ ^ 2 ≤ N →
    ∃ η : ℝ,
      η = ν - nonlinearCoefficient (‖v‖ ^ 2) (∑ j : Fin 3, ‖G j‖ ^ 2) ∧
      0 < η ∧
      4 * Real.pi ^ 2 * N ^ 4 ≤
        ((‖v‖ ^ 2) * (∑ j : Fin 3, ‖G j‖ ^ 2)) * (‖L‖ ^ 2) ^ 4 ∧
      N ≤ (ν - η) * ‖L‖ ^ 2 ∧
      d + 2 * η * ‖L‖ ^ 2 ≤ 0

/-- LE097 supplies every quantified field instance of PointwiseAbsorption.
LC001 implies the required LC002 internally; LC004/LC001/LC003 remain inputs.
-/
theorem pointwiseAbsorption_of_analytic_inputs
    {ν : ℝ} (hν : 0 < ν)
    (hExtension : CompactToSchwartzEndpoint)
    (hSpectral : WholeSpaceSpectralEndpoint)
    (hAgmon : WholeSpaceAgmonEndpoint) :
    PointwiseAbsorption ν := by
  intro v L G H N d hDerivatives hN hConvection hSmall hEnstrophy
  obtain ⟨_, _, _, η, _, _, hη, hηpos, hFourth, hNonlinear, hAbsorption⟩ :=
    QFA.Assembly.AnalyticChain.exists_absorption_of_compactData
      hExtension hSpectral hAgmon hDerivatives hN hConvection hν hSmall hEnstrophy
  exact ⟨η, hη, hηpos, hFourth, hNonlinear, hAbsorption⟩

/-- Explicit unresolved local-strong/temporal-invariant/continuation input.
Its output is the existing reference-witness construction, not tail equality,
a restricted singleton, smoothness or the frozen physical root conclusion.
No inhabitant of this proposition is supplied in this module.
-/
def ReferenceConstructionFromAbsorption
    (ν : ℝ) (Domain : Set RealSpatialL2)
    (Admissible : RealSpatialL2 → Set Trajectory)
    (Reference : RealSpatialL2 → Trajectory → Prop)
    (Good : Trajectory → GradientTrajectory → ℝ → Prop) : Prop :=
  PointwiseAbsorption ν →
    Chain.SubcriticalReferenceConstruction ν Domain Admissible Reference Good

/-- Canonical integrated implication: derive pointwise analytic absorption,
pass it to the explicit unresolved reference construction, and invoke the
complete class/reference tail assembly. The conclusion is exactly the
quantified conclusion of Chain.quantified_tail_assembly.
-/
theorem quantified_tail_assembly_of_analytic_inputs
    {ν : ℝ} {Domain : Set RealSpatialL2}
    {Admissible : RealSpatialL2 → Set Trajectory}
    {Reference : RealSpatialL2 → Trajectory → Prop}
    {Good : Trajectory → GradientTrajectory → ℝ → Prop}
    (hν : 0 < ν)
    (hClass : Chain.ClassRealization ν Domain Admissible Good)
    (hPorts : Chain.ReferencePorts Admissible Reference)
    (hExtension : CompactToSchwartzEndpoint)
    (hSpectral : WholeSpaceSpectralEndpoint)
    (hAgmon : WholeSpaceAgmonEndpoint)
    (hReferenceBackend :
      ReferenceConstructionFromAbsorption ν Domain Admissible Reference Good) :
    ∀ a ∈ Domain,
      (Admissible a).Nonempty ∧
      ∀ u ∈ Admissible a,
        u 0 = a ∧ Tendsto u (𝓝[>] (0 : ℝ)) (𝓝 a) ∧
        ∀ δ : ℝ, ‖a‖ ^ 4 / (16 * Real.pi ^ 2 * ν ^ 5) < δ →
          ∃ G : GradientTrajectory,
            EnergyProfile ν a u G ∧
              Chain.SelectedTail ν δ Admissible Reference u G (Good u G) := by
  have hAbsorption : PointwiseAbsorption ν :=
    pointwiseAbsorption_of_analytic_inputs hν hExtension hSpectral hAgmon
  exact Chain.quantified_tail_assembly hν hClass (hReferenceBackend hAbsorption) hPorts

end

end QFA.Assembly.Integrated
