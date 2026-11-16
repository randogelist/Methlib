import SingularClosure.GalerkinAlgebra
import SingularClosure.GalerkinExistence
import SingularClosure.CanonicalGalerkin
import SingularClosure.GalerkinEnergyIntegral
import SingularClosure.PeriodicPoincare
import SingularClosure.VAR_STABLE.Endpoints.Mathlib

/-!
# VAR_STABLE finite Galerkin and ODE endpoint collection

Existing finite polynomial vector field, existence, uniqueness, canonical
trajectory, exact energy identity, periodic spectral gap, and Mathlib ODE
comparison endpoints.
-/

set_option autoImplicit false

namespace SingularClosure
namespace VAR_STABLE

#check contDiff_finiteGalerkinRhs
#check GALERKIN_GLOBAL_EXISTS_UNIQUE
#check canonicalGalerkinSolution
#check GalerkinSolution.coeff_unique_forward
#check GalerkinSolution.velocity_unique_forward
#check GalerkinSolution.coefficientEnergy_integral_identity
#check COEFFICIENT_POINCARE
#check COEFFICIENT_GRADIENT_POINCARE
#check GalerkinSolution.physicalPoincare

end VAR_STABLE
end SingularClosure
