import ConcreteABCDUnifiedClosure

/-! Fefferman A. Both type checks refer to the named v0.25.0 declarations. -/

namespace Fefferman.ConcreteReal

example : WholeSpaceZeroForceGlobalRegularity → A realAnalysis :=
  wholeSpaceZeroForceGlobalRegularity_implies_A

example : WholeSpaceZeroForceGlobalRegularity ↔ A realAnalysis :=
  WHOLESPACE_ZERO_FORCE_GLOBAL_REGULARITY_IFF_A

end Fefferman.ConcreteReal
