import ConcreteABCDUnifiedClosure

/-! Fefferman B. Both type checks refer to the named v0.25.0 declarations. -/

namespace Fefferman.ConcreteReal

example : PeriodicZeroForceGlobalRegularity → B realAnalysis :=
  periodicZeroForceGlobalRegularity_implies_B

example : PeriodicZeroForceGlobalRegularity ↔ B realAnalysis :=
  PERIODIC_ZERO_FORCE_GLOBAL_REGULARITY_IFF_B

end Fefferman.ConcreteReal
