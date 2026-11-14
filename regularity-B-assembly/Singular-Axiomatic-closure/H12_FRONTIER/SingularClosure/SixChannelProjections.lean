import SingularClosure.SmoothSixFourier
import SingularClosure.SmoothSixSynthesis
import SingularClosure.SmoothSixOrthogonal

/-!
# The six physical projection endpoint

The maps are the literal coordinate averages at axes 2 and 0 defined in
`SmoothSixChannels`. The Fourier cutoff below uses the actual cube Fourier
coefficients of its physical input. Every clause is proved for those maps.
-/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory
open scoped BigOperators ContDiff

namespace SingularClosure

noncomputable section

/-- Physical Fourier cutoff on the nonzero Euclidean frequency ball. -/
def physicalFourierCutoff (N : ℕ) (a : Field) : Field :=
  finiteSynthesis N (datumFourierCoeff a)

theorem smoothSixChannel_fourierCutoff (A : Fin 6) (N : ℕ) (a : Field)
    (ha : Continuous a) :
    smoothSixChannel A (physicalFourierCutoff N a) =
      physicalFourierCutoff N (smoothSixChannel A a) := by
  unfold physicalFourierCutoff
  rw [smoothSixChannel_finiteSynthesis, datumFourierCoeff_smoothSixChannel A a ha]

/-- The exact physical laws collected by the frozen projection endpoint. -/
structure PhysicalSixChannelProjectionLaws : Prop where
  reconstruction : ∀ a : Field, (∑ A : Fin 6, smoothSixChannel A a) = a
  additive : ∀ (A : Fin 6) (a b : Field), Continuous a → Continuous b →
    smoothSixChannel A (a + b) = smoothSixChannel A a + smoothSixChannel A b
  homogeneous : ∀ (A : Fin 6) (r : ℝ) (a : Field),
    smoothSixChannel A (r • a) = r • smoothSixChannel A a
  idempotent : ∀ (A : Fin 6) (a : Field), Continuous a →
    smoothSixChannel A (smoothSixChannel A a) = smoothSixChannel A a
  disjoint : ∀ (A B : Fin 6), A ≠ B → ∀ a : Field, Continuous a →
    smoothSixChannel A (smoothSixChannel B a) = 0
  selfAdjoint : ∀ (A : Fin 6) (a b : Field),
    ContDiff ℝ ∞ a → ContDiff ℝ ∞ b →
    (∫ x in unitCube, inner ℝ (smoothSixChannel A a x) (b x)) =
      ∫ x in unitCube, inner ℝ (a x) (smoothSixChannel A b x)
  orthogonal : ∀ (A B : Fin 6), A ≠ B → ∀ a b : Field,
    ContDiff ℝ ∞ a → ContDiff ℝ ∞ b →
    (∫ x in unitCube, inner ℝ (smoothSixChannel A a x) (smoothSixChannel B b x)) = 0
  preserves_smoothSigmaZero : ∀ (A : Fin 6) (a : Field),
    SmoothSigmaZero a → SmoothSigmaZero (smoothSixChannel A a)
  commutes_derivative : ∀ (A : Fin 6) (i : Fin 3) (a : Field),
    ContDiff ℝ ∞ a → SpatialPeriodic a →
    coordinateDerivative (smoothSixChannel A a) i =
      smoothSixChannel A (coordinateDerivative a i)
  commutes_fourierCutoff : ∀ (A : Fin 6) (N : ℕ) (a : Field), Continuous a →
    smoothSixChannel A (physicalFourierCutoff N a) =
      physicalFourierCutoff N (smoothSixChannel A a)

/-- Full physical projection endpoint, with no certificate or analytic premise. -/
theorem SIX_CHANNEL_PROJECTIONS : PhysicalSixChannelProjectionLaws where
  reconstruction := SMOOTH_SIX_CHANNEL_RECONSTRUCTION
  additive := smoothSixChannel_add
  homogeneous := smoothSixChannel_smul
  idempotent := smoothSixChannel_idempotent
  disjoint := smoothSixChannel_disjoint
  selfAdjoint := smoothSixChannel_selfAdjoint
  orthogonal := smoothSixChannel_orthogonal
  preserves_smoothSigmaZero := smoothSixChannel_preserves_smoothSigmaZero
  commutes_derivative := smoothSixChannel_coordinateDerivative
  commutes_fourierCutoff := smoothSixChannel_fourierCutoff

end

end SingularClosure
