import Mathlib.Analysis.Distribution.FourierMultiplier
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# QFA: whole-space Agmon endpoint contracts

Definitions of Prop targets only. No theorem below asserts that these targets
are inhabited. The physical analytic adapters remain pending Lean bodies.

Source pin: Mathlib db584cd6d46c92f209a44c0f1c829460d327499d, Lean 4.33.0.
No local Lean execution; no external compiler or axiom-audit evidence.

Pending adapters are explicit:
* AD01: actual real fields and their weak derivatives -> isometric complex L2 data.
* AD08: compact-test physical derivative identities -> the Schwartz derivative
  witnesses below -> noncircular construction of weighted Fourier L2 witnesses.
* AD03: the L1 inverse Fourier representative agrees a.e. with the L2 inverse.

The full-volume, three-dimensional, Hilbert-vector geometry is fixed here.
The gradient energy is a sum of three squared L2 directional norms, not the
operator norm of a Frechet derivative.
-/

set_option autoImplicit false
set_option Elab.async true

open MeasureTheory
open scoped FourierTransform SchwartzMap LineDeriv Laplacian BoundedContinuousFunction

namespace QFA.Endpoints.Agmon

noncomputable section

abbrev Space := EuclideanSpace ℝ (Fin 3)
abbrev ComplexVector := EuclideanSpace ℂ (Fin 3)
abbrev ComplexL2 := Lp ComplexVector 2 (volume : Measure Space)

def velocityEnergy (v : ComplexL2) : ℝ := ‖v‖ ^ 2

def gradientEnergy (G : Fin 3 → ComplexL2) : ℝ :=
  ∑ j : Fin 3, ‖G j‖ ^ 2

def laplacianEnergy (L : ComplexL2) : ℝ := ‖L‖ ^ 2

/-- Existing L2 fields witnessing derivatives in the Schwartz-distribution sense.

This is not a theorem converting compact-test weak derivatives into these
witnesses. That conversion is the explicit pending AD08 adapter.
-/
structure SchwartzDerivativeWitnesses
    (v : ComplexL2) (G : Fin 3 → ComplexL2) (L : ComplexL2) : Prop where
  gradient_eq : ∀ j : Fin 3,
    (G j : 𝓢'(Space, ComplexVector)) =
      ∂_{EuclideanSpace.basisFun (Fin 3) ℝ j} (v : 𝓢'(Space, ComplexVector))
  laplacian_eq :
    (L : 𝓢'(Space, ComplexVector)) = Δ (v : 𝓢'(Space, ComplexVector))

/-- Exact native-Fourier spectral outputs, including genuine integrability.

EP047--EP061 and AD08 are the selected inputs for a future proof. The native
Fourier character is exp(-2*pi*i*<x,k>), so the weights retain every 2*pi factor.
-/
structure NativeSpectralRealization
    (v : ComplexL2) (G : Fin 3 → ComplexL2) (L : ComplexL2) : Prop where
  energy_integrable :
    Integrable (fun k : Space => ‖(𝓕 v : ComplexL2) k‖ ^ 2) volume
  gradient_integrable :
    Integrable (fun k : Space =>
      (2 * Real.pi) ^ 2 * ‖k‖ ^ 2 * ‖(𝓕 v : ComplexL2) k‖ ^ 2) volume
  laplacian_integrable :
    Integrable (fun k : Space =>
      (2 * Real.pi) ^ 4 * ‖k‖ ^ 4 * ‖(𝓕 v : ComplexL2) k‖ ^ 2) volume
  energy_identity :
    velocityEnergy v = ∫ k : Space, ‖(𝓕 v : ComplexL2) k‖ ^ 2
  gradient_identity :
    gradientEnergy G =
      ∫ k : Space, (2 * Real.pi) ^ 2 * ‖k‖ ^ 2 * ‖(𝓕 v : ComplexL2) k‖ ^ 2
  laplacian_identity :
    laplacianEnergy L =
      ∫ k : Space, (2 * Real.pi) ^ 4 * ‖k‖ ^ 4 * ‖(𝓕 v : ComplexL2) k‖ ^ 2

/-- PENDING ANALYTIC PROP TARGET: AD08 with actual L2 derivative witnesses. -/
def WholeSpaceSpectralEndpoint : Prop :=
  ∀ (v : ComplexL2) (G : Fin 3 → ComplexL2) (L : ComplexL2),
    SchwartzDerivativeWitnesses v G L → NativeSpectralRealization v G L

/-- PENDING ANALYTIC PROP TARGET: D06.07 in physical squared-energy notation. -/
def WholeSpaceInterpolationEndpoint : Prop :=
  ∀ (v : ComplexL2) (G : Fin 3 → ComplexL2) (L : ComplexL2),
    SchwartzDerivativeWitnesses v G L →
      gradientEnergy G ^ 2 ≤ velocityEnergy v * laplacianEnergy L

/-- PENDING ANALYTIC PROP TARGET: exact vector Agmon constant and representative.

EP063--EP071 give the selected radial/integral ingredients; AD03 supplies the
a.e. representative identification. No component-count factor is introduced.
-/
def WholeSpaceAgmonEndpoint : Prop :=
  ∀ (v : ComplexL2) (G : Fin 3 → ComplexL2) (L : ComplexL2),
    SchwartzDerivativeWitnesses v G L →
      ∃ V : Space →ᵇ ComplexVector,
        (fun x : Space => V x) =ᵐ[volume] (fun x : Space => v x) ∧
        ‖V‖ ^ 2 ≤ Real.sqrt (gradientEnergy G * laplacianEnergy L) / (2 * Real.pi)

end

end QFA.Endpoints.Agmon
