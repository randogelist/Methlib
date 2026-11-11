import SingularClosure.GalerkinInvariant
import SingularClosure.GalerkinExistence
import SingularClosure.InitialFourier

/-!
# Frozen endpoint 3: actual global Galerkin existence and forward uniqueness

The coefficient data are the literal Fourier integrals of the smooth physical
input. Their integrability, conjugate reality and solenoidality are proved in
InitialFourier; the invariant finite-dimensional dissipative ODE is constructed
in GalerkinInvariant. Uniqueness is equality on the physical time domain [0,∞).
The values assigned at negative times are outside the trajectory contract.
-/

set_option autoImplicit false

open Set

namespace SingularClosure

noncomputable section

theorem GALERKIN_GLOBAL_EXISTS_UNIQUE (ν : ℝ) (hν : 0 < ν)
    (a : Field) (ha : SmoothSigmaZero a) (N : ℕ) :
    ∃ g : GalerkinSolution ν a N, ∀ h : GalerkinSolution ν a N,
      EqOn g.coeff h.coeff (Ici 0) := by
  obtain ⟨g⟩ := galerkinSolution_exists_of_fourier_invariants ν hν.le a N
    (smoothSigmaZero_fourier_integrable ha)
    (datumFourierCoeff_reality a) (smoothSigmaZero_fourier_solenoidal ha)
  exact ⟨g, fun h => g.coeff_unique_forward h⟩

end

end SingularClosure
