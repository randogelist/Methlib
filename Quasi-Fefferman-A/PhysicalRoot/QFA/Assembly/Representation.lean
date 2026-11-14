import QFA.Endpoints.Representation.Complexification

/-!
# QFA assembly: supplied compact-test derivative data

Status: A_TIER_CANDIDATE. No local Lean or Lake execution.
External baseline: Lean 4.33.0, Mathlib
db584cd6d46c92f209a44c0f1c829460d327499d; cached compilation and exact
declaration-level axiom auditing remain pending.

D02.03: existing LE050 transports each supplied first and second directional
weak derivative. Actual L2 linearity assembles the supplied Laplacian sum.
D06.02: compact-to-Schwartz extension and spectral realization are separate
named Prop inputs. Neither is supplied with a proof inhabitant here.

The spatial domain and measure are exactly the existing full-volume R3
carriers. The data below do not assert existence of derivatives for an
arbitrary field or membership of a trajectory in the Leray-Hopf class.
-/

set_option autoImplicit false
set_option Elab.async true

open MeasureTheory
open scoped BigOperators

namespace QFA.Assembly.Representation

open QFA.Endpoints.Agmon
open QFA.Endpoints.Representation

noncomputable section

/-- Supplied first derivatives, diagonal second derivatives, and their actual
L2 sum. All derivative identities use real smooth compactly supported tests.
The diagonal witnesses are sufficient to specify the weak Laplacian sum;
no unproved compact-to-Schwartz conversion is included in this structure.
-/
structure CompactDerivativeData
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (v : Lp F 2 (volume : Measure Space))
    (G H : Fin 3 → Lp F 2 (volume : Measure Space))
    (L : Lp F 2 (volume : Measure Space)) : Prop where
  gradient : ∀ j : Fin 3,
    RealTestWeakDirectionalDerivative v (G j)
      (EuclideanSpace.basisFun (Fin 3) ℝ j)
  diagonal_second : ∀ j : Fin 3,
    RealTestWeakDirectionalDerivative (G j) (H j)
      (EuclideanSpace.basisFun (Fin 3) ℝ j)
  laplacian_sum : L = ∑ j : Fin 3, H j

/-- Finite-sum compatibility of the already constructed real linear L2 isometry. -/
theorem complexifyL2_sum (H : Fin 3 → RealL2) :
    complexifyL2 (∑ j : Fin 3, H j) = ∑ j : Fin 3, complexifyL2 (H j) := by
  change complexifyL2LI.toLinearMap (∑ j : Fin 3, H j) =
    ∑ j : Fin 3, complexifyL2LI.toLinearMap (H j)
  exact map_sum complexifyL2LI.toLinearMap H Finset.univ

/-- Assemble first/second derivative transport and the actual Laplacian sum.
LE050 is applied to each existing derivative witness, with no witness invention.
-/
theorem complexify_compactDerivativeData
    {v L : RealL2} {G H : Fin 3 → RealL2}
    (h : CompactDerivativeData v G H L) :
    CompactDerivativeData (complexifyL2 v)
      (fun j => complexifyL2 (G j)) (fun j => complexifyL2 (H j))
      (complexifyL2 L) := by
  refine ⟨?_, ?_, ?_⟩
  · intro j
    exact complexifyL2_weakDirectionalDerivative (h.gradient j)
  · intro j
    exact complexifyL2_weakDirectionalDerivative (h.diagonal_second j)
  · rw [h.laplacian_sum]
    exact complexifyL2_sum H

/-- PENDING ANALYTIC PROP TARGET: AD08's extension from actual compact-real-test
data to the existing Schwartz-distribution derivative witnesses.
No proof of this universally quantified proposition is supplied in this module.
-/
def CompactToSchwartzEndpoint : Prop :=
  ∀ (v : ComplexL2) (G H : Fin 3 → ComplexL2) (L : ComplexL2),
    CompactDerivativeData v G H L → SchwartzDerivativeWitnesses v G L

/-- Conditional assembly of the compact-test transport and the explicit
extension endpoint. The extension premise remains visible in the theorem type.
-/
theorem schwartzWitnesses_of_compactData
    (hExtension : CompactToSchwartzEndpoint)
    {v L : RealL2} {G H : Fin 3 → RealL2}
    (h : CompactDerivativeData v G H L) :
    SchwartzDerivativeWitnesses (complexifyL2 v)
      (fun j => complexifyL2 (G j)) (complexifyL2 L) :=
  hExtension (complexifyL2 v) (fun j => complexifyL2 (G j))
    (fun j => complexifyL2 (H j)) (complexifyL2 L)
    (complexify_compactDerivativeData h)

/-- Actual spectral target assembly from supplied derivative data and two
named analytic endpoints. This theorem does not discharge either endpoint.
-/
theorem spectralRealization_of_compactData
    (hExtension : CompactToSchwartzEndpoint)
    (hSpectral : WholeSpaceSpectralEndpoint)
    {v L : RealL2} {G H : Fin 3 → RealL2}
    (h : CompactDerivativeData v G H L) :
    NativeSpectralRealization (complexifyL2 v)
      (fun j => complexifyL2 (G j)) (complexifyL2 L) :=
  hSpectral (complexifyL2 v) (fun j => complexifyL2 (G j))
    (complexifyL2 L) (schwartzWitnesses_of_compactData hExtension h)

end

end QFA.Assembly.Representation
