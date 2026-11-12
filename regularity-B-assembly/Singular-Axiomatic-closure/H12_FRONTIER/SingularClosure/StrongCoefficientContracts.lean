import SingularClosure.FourierTransport
import SingularClosure.SmoothDatumSobolev

/-!
# Concrete strong Fourier trajectory contract

Every coefficient operation is explicit. The transport series is the actual
absolutely convergent convolution constructed in `FourierTransport`. The
contract includes genuine Hilbert-valued Bochner membership and an integral
identity identifying the time derivative. It asserts neither existence nor
the still separate physical PDE realization theorem.
-/

set_option autoImplicit false

open Set MeasureTheory
open scoped ENNReal Interval

namespace SingularClosure

noncomputable section

def fullFourierRhs (ν : ℝ) (c : TorusSobolev 0)
    (k : Frequency) (i : Fin 3) : ℂ :=
  -((ν * (2 * Real.pi) ^ 2 * (galerkinFreqSq k : ℝ) : ℝ) : ℂ) * c.val k i -
    coefficientLeray k (fun j => divergenceTransportCoefficient k j c c) i

/-- The literal global strong coefficient equation; no analytic adapter or
regularity conclusion is stored as a premise. -/
structure GlobalStrongCoefficientNSE (ν : ℝ) (a : Field)
    (ha : SmoothSigmaZero a) where
  state : ℝ → TorusSobolev 1
  stateH2 : ℝ → TorusSobolev 2
  derivativeH0 : ℝ → TorusSobolev 0
  continuous : ContinuousOn state (Ici 0)
  initial : state 0 = smoothDatumSobolev 1 a ha.smooth ha.periodic
  local_H1 : ∀ T : ℝ, 0 < T →
    MemLp state ⊤ (volume.restrict (Icc (0 : ℝ) T))
  local_H2 : ∀ T : ℝ, 0 < T →
    MemLp stateH2 2 (volume.restrict (Icc (0 : ℝ) T))
  local_derivative : ∀ T : ℝ, 0 < T →
    MemLp derivativeH0 2 (volume.restrict (Icc (0 : ℝ) T))
  H2_agreement : ∀ T : ℝ, 0 < T →
    ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T),
      torusSobolevInclusion 1 (stateH2 t) = state t
  derivative_integrable : ∀ T : ℝ, 0 ≤ T →
    IntervalIntegrable derivativeH0 volume 0 T
  time_integral : ∀ t : ℝ, 0 ≤ t →
    torusSobolevInclusion 0 (state t) =
      torusSobolevInclusion 0 (state 0) + ∫ s in (0 : ℝ)..t, derivativeH0 s
  equation : ∀ T : ℝ, 0 < T →
    ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T),
      ∀ k : Frequency, ∀ i : Fin 3,
        (derivativeH0 t).val k i =
          fullFourierRhs ν (torusSobolevInclusion 0 (state t)) k i
  reality : ∀ t : ℝ, 0 ≤ t → SpectralReality (state t).val
  solenoidal : ∀ t : ℝ, 0 ≤ t → SpectralSolenoidal (state t).val
  mean_zero : ∀ t : ℝ, 0 ≤ t → SpectralMeanZero (state t).val

end

end SingularClosure
