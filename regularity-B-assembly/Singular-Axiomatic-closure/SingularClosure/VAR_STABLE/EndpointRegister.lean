import SingularClosure.VAR_STABLE.Endpoints.All

/-!
# VAR_STABLE endpoint register

Staging module only.

The existing Mathlib and Methlib dependencies are gathered under:

`SingularClosure/VAR_STABLE/Endpoints/`

No new theorem is asserted by this file. The principal future root is:

`FINITE_ENTRY_AX6_IMP_GLOBAL_REGULARITY`

Dependency order:

1. `AX6At`
2. `LOCAL_AX6_TO_STRONG_SOLUTION_THROUGH`
3. `CRITICAL_ENERGY_ZERO_ONE_TWO_INTERPOLATION`
4. `EXPLICIT_CRITICAL_ENTRY_HORIZON`
5. `STRONG_TRACE_TO_CRITICAL_DATUM`
6. `SMALL_CRITICAL_SOLUTION_TIME_SHIFT`
7. `SMALL_CRITICAL_RESTART_SPLICE`
8. `FINITE_ENTRY_AX6_IMP_GLOBAL_REGULARITY`

Prepared declarations do not establish A-tier status. Promotion requires a
matching external compiler transcript and theorem-level axiom audit.
-/

set_option autoImplicit false
set_option Elab.async true

namespace SingularClosure
namespace VAR_STABLE

-- New formal declarations will be introduced in dependency order.

end VAR_STABLE
end SingularClosure
