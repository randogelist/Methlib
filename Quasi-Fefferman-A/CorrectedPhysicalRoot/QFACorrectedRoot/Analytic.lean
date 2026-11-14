import QFALC005
import QFA.Assembly.Integrated

/-!
# QFA corrected analytic chain

The input derivative identities are stated directly on the mathematically
separating class of compactly supported Schwartz tests. LC005 and the
compact-Schwartz-to-tempered-distribution bridge are imported as proved
results. The invalid universal extension from the old radial bump predicate is
not a premise.

The spectral and Agmon endpoints and the passage from pointwise absorption to
a global strong reference remain explicit premises.
-/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory Filter
open scoped BigOperators BoundedContinuousFunction Topology

namespace QFA.CorrectedPhysicalRoot

open QFA.Endpoints.Agmon
open QFA.Endpoints.Representation
open QFA.Endpoints.Representation.CompactSchwartz
open QFA.Assembly.AnalyticInputs
open QFA.Assembly.AnalyticChain
open QFA.Assembly.Chain
open QFA.Representation

noncomputable section

/-- Corrected pointwise analytic input: the derivative identities are supplied
on compactly supported Schwartz tests rather than on the old radial bump
family. The conclusion is the same exact nonlinear absorption statement used
by the reference-construction backend.
-/
def CorrectedPointwiseAbsorption (ν : ℝ) : Prop :=
  ∀ (v L : RealL2) (G : Fin 3 → RealL2) (N d : ℝ),
    CompactSchwartzDerivativeWitnesses (complexifyL2 v)
      (fun j => complexifyL2 (G j)) (complexifyL2 L) →
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

/-- Pointwise absorption from compact-Schwartz derivative data, the spectral
realization endpoint and the Agmon endpoint. LC005 and distributional
extension are discharged by the imported A-tier chain.
-/
theorem exists_absorption_of_compactSchwartzData
    (hSpectral : WholeSpaceSpectralEndpoint)
    (hAgmon : WholeSpaceAgmonEndpoint)
    {v L : RealL2} {G : Fin 3 → RealL2} {N d ν : ℝ}
    (hDerivatives : CompactSchwartzDerivativeWitnesses (complexifyL2 v)
      (fun j => complexifyL2 (G j)) (complexifyL2 L))
    (hN : 0 ≤ N)
    (hConvection : ∀ V : Space →ᵇ ComplexVector,
      (fun x : Space => V x) =ᵐ[volume] (fun x : Space => complexifyL2 v x) →
        N ≤ ‖V‖ * Real.sqrt (∑ j : Fin 3, ‖G j‖ ^ 2) * Real.sqrt (‖L‖ ^ 2))
    (hν : 0 < ν)
    (hSmall : (‖v‖ ^ 2) * (∑ j : Fin 3, ‖G j‖ ^ 2) < 4 * Real.pi ^ 2 * ν ^ 4)
    (hEnstrophy : d / 2 + ν * ‖L‖ ^ 2 ≤ N) :
    ∃ η : ℝ,
      η = ν - nonlinearCoefficient (‖v‖ ^ 2) (∑ j : Fin 3, ‖G j‖ ^ 2) ∧
      0 < η ∧
      4 * Real.pi ^ 2 * N ^ 4 ≤
        ((‖v‖ ^ 2) * (∑ j : Fin 3, ‖G j‖ ^ 2)) * (‖L‖ ^ 2) ^ 4 ∧
      N ≤ (ν - η) * ‖L‖ ^ 2 ∧
      d + 2 * η * ‖L‖ ^ 2 ≤ 0 := by
  have hSchwartz : SchwartzDerivativeWitnesses (complexifyL2 v)
      (fun j => complexifyL2 (G j)) (complexifyL2 L) :=
    schwartzDerivativeWitnesses_of_compactSchwartz_unconditional hDerivatives
  obtain ⟨V, hV, hProfile⟩ := exists_scalarProfile_of_analytic_endpoints
    (interpolationEndpoint_of_spectralEndpoint hSpectral) hAgmon hSchwartz hN
    (by
      intro V hV
      simpa only [complexifyL2_gradientEnergy, complexifyL2_laplacianEnergy]
        using hConvection V hV)
  have hProfileReal :
      ScalarProfile (‖v‖ ^ 2) (∑ j : Fin 3, ‖G j‖ ^ 2) (‖L‖ ^ 2) ‖V‖ N := by
    simpa only [complexifyL2_velocityEnergy, complexifyL2_gradientEnergy,
      complexifyL2_laplacianEnergy] using hProfile
  refine ⟨ν - nonlinearCoefficient (‖v‖ ^ 2) (∑ j : Fin 3, ‖G j‖ ^ 2),
    rfl, hProfileReal.viscosity_margin_pos hν hSmall,
    hProfileReal.nonlinear_fourth_power, ?_,
    hProfileReal.enstrophy_absorption hEnstrophy⟩
  have hCoefficient : ν -
      (ν - nonlinearCoefficient (‖v‖ ^ 2) (∑ j : Fin 3, ‖G j‖ ^ 2)) =
      nonlinearCoefficient (‖v‖ ^ 2) (∑ j : Fin 3, ‖G j‖ ^ 2) := by ring
  simpa only [hCoefficient] using hProfileReal.nonlinear_le_coefficient

/-- The corrected universally quantified absorption theorem. -/
theorem correctedPointwiseAbsorption_of_analytic_inputs
    {ν : ℝ} (hν : 0 < ν)
    (hSpectral : WholeSpaceSpectralEndpoint)
    (hAgmon : WholeSpaceAgmonEndpoint) :
    CorrectedPointwiseAbsorption ν := by
  intro v L G N d hDerivatives hN hConvection hSmall hEnstrophy
  exact exists_absorption_of_compactSchwartzData hSpectral hAgmon
    hDerivatives hN hConvection hν hSmall hEnstrophy

/-- Explicit unresolved physical backend. It must construct the global
reference from the corrected pointwise absorption statement, including the
physical compact-Schwartz derivative identities, local strong evolution,
temporal invariant and continuation.
-/
def CorrectedReferenceConstructionFromAbsorption
    (ν : ℝ) (Domain : Set RealSpatialL2)
    (Admissible : RealSpatialL2 → Set Trajectory)
    (Reference : RealSpatialL2 → Trajectory → Prop)
    (Good : Trajectory → GradientTrajectory → ℝ → Prop) : Prop :=
  CorrectedPointwiseAbsorption ν →
    SubcriticalReferenceConstruction ν Domain Admissible Reference Good

/-- Corrected quantified tail assembly with no old compact-to-Schwartz premise. -/
theorem quantified_tail_assembly_of_corrected_analytic_inputs
    {ν : ℝ} {Domain : Set RealSpatialL2}
    {Admissible : RealSpatialL2 → Set Trajectory}
    {Reference : RealSpatialL2 → Trajectory → Prop}
    {Good : Trajectory → GradientTrajectory → ℝ → Prop}
    (hν : 0 < ν)
    (hClass : ClassRealization ν Domain Admissible Good)
    (hPorts : ReferencePorts Admissible Reference)
    (hSpectral : WholeSpaceSpectralEndpoint)
    (hAgmon : WholeSpaceAgmonEndpoint)
    (hReferenceBackend :
      CorrectedReferenceConstructionFromAbsorption
        ν Domain Admissible Reference Good) :
    ∀ a ∈ Domain,
      (Admissible a).Nonempty ∧
      ∀ u ∈ Admissible a,
        u 0 = a ∧ Tendsto u (𝓝[>] (0 : ℝ)) (𝓝 a) ∧
        ∀ δ : ℝ, ‖a‖ ^ 4 / (16 * Real.pi ^ 2 * ν ^ 5) < δ →
          ∃ G : GradientTrajectory,
            EnergyProfile ν a u G ∧
              SelectedTail ν δ Admissible Reference u G (Good u G) := by
  have hAbsorption : CorrectedPointwiseAbsorption ν :=
    correctedPointwiseAbsorption_of_analytic_inputs hν hSpectral hAgmon
  exact quantified_tail_assembly hν hClass (hReferenceBackend hAbsorption) hPorts

end

end QFA.CorrectedPhysicalRoot
