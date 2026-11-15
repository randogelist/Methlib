import SingularClosure.Root
import SingularClosure.NoetherClosure.AX6Bridge

/-!
NC05: deterministic final conditional composition.
The root is NOT unconditional; NOETHER_CHARGE_ADMISSION is an explicit premise.
-/
set_option autoImplicit false
set_option Elab.async true

namespace SingularClosure

theorem NOETHER_CLOSURE :
    NOETHER_CHARGE_ADMISSION → Fefferman_B_0_adjust := by
  intro hNoether
  exact ax6_implies_fefferman_B_0_adjust (NOETHER_TO_AX6 hNoether)

end SingularClosure
