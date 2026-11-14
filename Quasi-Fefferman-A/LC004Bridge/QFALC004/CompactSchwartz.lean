import QFA.Endpoints.Agmon.Contracts
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic

/-!
# QFA: corrected compact-test to Schwartz-distribution bridge

The pre-existing `RealTestWeakDirectionalDerivative` predicate quantifies over
`ContDiffBump`, a structured radial cutoff family. That family is not used here
as a density surrogate.

This module records the exact sufficient compact-test interface: equality on
all compactly supported Schwartz tests, together with density of that test
class in the Schwartz topology. The bridge to equality of tempered
distributions is then purely topological and linear.

Status before matching external evidence: A_TIER_CANDIDATE.
Source baseline: Lean 4.33.0, Mathlib
`db584cd6d46c92f209a44c0f1c829460d327499d`.
-/

set_option autoImplicit false
set_option Elab.async true

open Set
open scoped SchwartzMap LineDeriv Laplacian

namespace QFA.Endpoints.Representation.CompactSchwartz

open QFA.Endpoints.Agmon

noncomputable section

/-- Compactly supported scalar Schwartz tests. -/
def compactSchwartzTests : Set 𝓢(Space, ℂ) :=
  {φ | HasCompactSupport (φ : Space → ℂ)}

/-- The precise density premise required by the corrected compact-test bridge. -/
def DenseCompactSchwartzTests : Prop :=
  Dense compactSchwartzTests

/-- Existing L2 derivative fields agree with the required distributional
operators on every compactly supported Schwartz test.
-/
structure CompactSchwartzDerivativeWitnesses
    (v : ComplexL2) (G : Fin 3 → ComplexL2) (L : ComplexL2) : Prop where
  gradient_eq_on_compact : ∀ (j : Fin 3) (φ : 𝓢(Space, ℂ)),
    φ ∈ compactSchwartzTests →
      (G j : 𝓢'(Space, ComplexVector)) φ =
        (∂_{EuclideanSpace.basisFun (Fin 3) ℝ j}
          (v : 𝓢'(Space, ComplexVector))) φ
  laplacian_eq_on_compact : ∀ φ : 𝓢(Space, ℂ),
    φ ∈ compactSchwartzTests →
      (L : 𝓢'(Space, ComplexVector)) φ =
        (Δ (v : 𝓢'(Space, ComplexVector))) φ

/-- A dense set remains dense after inclusion into its linear span. -/
theorem dense_span_compactSchwartzTests
    (hDense : DenseCompactSchwartzTests) :
    Dense (Submodule.span ℂ compactSchwartzTests : Set 𝓢(Space, ℂ)) := by
  exact hDense.mono Submodule.subset_span

/-- Two tempered distributions that agree on every compactly supported
Schwartz test agree everywhere, conditional only on density of that test class.
-/
theorem tempered_eq_of_eq_on_compactSchwartz
    (hDense : DenseCompactSchwartzTests)
    {T U : 𝓢'(Space, ComplexVector)}
    (hEq : Set.EqOn T U compactSchwartzTests) :
    T = U := by
  exact ContinuousLinearMap.ext_on (dense_span_compactSchwartzTests hDense) hEq

/-- Correct compact-test identities imply the native
`SchwartzDerivativeWitnesses` contract.
-/
theorem schwartzDerivativeWitnesses_of_compactSchwartz
    (hDense : DenseCompactSchwartzTests)
    {v : ComplexL2} {G : Fin 3 → ComplexL2} {L : ComplexL2}
    (h : CompactSchwartzDerivativeWitnesses v G L) :
    SchwartzDerivativeWitnesses v G L := by
  constructor
  · intro j
    exact tempered_eq_of_eq_on_compactSchwartz hDense
      (fun φ hφ => h.gradient_eq_on_compact j φ hφ)
  · exact tempered_eq_of_eq_on_compactSchwartz hDense
      (fun φ hφ => h.laplacian_eq_on_compact φ hφ)

/-- Corrected replacement interface for the old `CompactToSchwartzEndpoint`.
It uses a mathematically separating compact test class and keeps density as an
explicit named premise.
-/
def CorrectedCompactToSchwartzEndpoint : Prop :=
  DenseCompactSchwartzTests →
    ∀ (v : ComplexL2) (G : Fin 3 → ComplexL2) (L : ComplexL2),
      CompactSchwartzDerivativeWitnesses v G L →
        SchwartzDerivativeWitnesses v G L

/-- The corrected endpoint follows from the topological density bridge. -/
theorem correctedCompactToSchwartzEndpoint :
    CorrectedCompactToSchwartzEndpoint := by
  intro hDense v G L h
  exact schwartzDerivativeWitnesses_of_compactSchwartz hDense h

end

end QFA.Endpoints.Representation.CompactSchwartz
