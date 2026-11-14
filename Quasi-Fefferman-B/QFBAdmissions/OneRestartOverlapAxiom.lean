import QFBBridge.FeffermanBClosure

/-!
The single named unresolved analytic axiom and the resulting conditional
Fefferman--B theorem.  The implication theorem itself is proved in
`QFBBridge.FeffermanBClosure`.
-/

set_option autoImplicit false
set_option Elab.async true

namespace QuasiFeffermanB

axiom QFB_ONE_RESTART_OVERLAP : QFBOneRestartOverlapStatement

theorem FEFFERMAN_B_CONDITIONAL_CLOSURE : FeffermanBStatement :=
  FEFFERMAN_B_OF_QFB_ONE_RESTART_OVERLAP QFB_ONE_RESTART_OVERLAP

end QuasiFeffermanB
