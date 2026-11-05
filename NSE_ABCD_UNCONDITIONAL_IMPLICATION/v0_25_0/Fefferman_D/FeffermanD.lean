import ConcreteABCDUnifiedClosure

/-! Fefferman D. Both type checks refer to the named v0.25.0 declarations. -/

namespace Fefferman.ConcreteReal

example : PeriodicForcedBreakdown → D realAnalysis :=
  periodicForcedBreakdown_implies_D

example : PeriodicForcedBreakdown ↔ D realAnalysis :=
  PERIODIC_FORCED_BREAKDOWN_IFF_D

end Fefferman.ConcreteReal
