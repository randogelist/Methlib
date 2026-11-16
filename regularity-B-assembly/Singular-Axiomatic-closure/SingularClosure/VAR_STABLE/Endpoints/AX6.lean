import SingularClosure.Admission
import SingularClosure.Ax6ExactBudget
import SingularClosure.StrongAccumulation
import SingularClosure.StrongTimeBounds
import SingularClosure.UniformStrongBounds
import SingularClosure.HighOrderAccumulation
import SingularClosure.HighOrderArzelaAscoli
import SingularClosure.HighOrderDiagonal
import SingularClosure.GlobalStrongLimit
import SingularClosure.GlobalSmoothBootstrap
import SingularClosure.PeriodicPressureRecovery
import SingularClosure.Root

/-!
# VAR_STABLE AX6 endpoint collection

Existing Methlib endpoints used after a finite-horizon VAR_STABLE certificate
has supplied the AX6 square-enstrophy budget.

No local `AX6At` theorem is introduced by this module.
-/

set_option autoImplicit false

namespace SingularClosure
namespace VAR_STABLE

#check AX6Statement
#check AX6_EXACT_REAL_SQUARE_BUDGET
#check AX6_UNIFORM_ENSTROPHY_ACCUMULATION
#check AX6_UNIFORM_PHYSICAL_ENSTROPHY_ACCUMULATION
#check AX6_UNIFORM_TIME_DERIVATIVE_BOUND
#check AX6_UNIFORM_PHYSICAL_STRONG_BOUNDS
#check AX6_UNIFORM_HIGH_ORDER_ACCUMULATION
#check GALERKIN_GLOBAL_STRONG_LIMIT
#check GLOBAL_STRONG_SMOOTH_BOOTSTRAP
#check PERIODIC_PRESSURE_RECOVERY
#check ax6_implies_fefferman_B_0_adjust

end VAR_STABLE
end SingularClosure
