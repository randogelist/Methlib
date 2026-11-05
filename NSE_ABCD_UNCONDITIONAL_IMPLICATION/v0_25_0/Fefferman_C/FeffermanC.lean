import ConcreteABCDUnifiedClosure

/-! Fefferman C. Both type checks refer to the named v0.25.0 declarations. -/

namespace Fefferman.ConcreteReal

example : WholeSpaceForcedBreakdown → C realAnalysis :=
  wholeSpaceForcedBreakdown_implies_C

example : WholeSpaceForcedBreakdown ↔ C realAnalysis :=
  WHOLESPACE_FORCED_BREAKDOWN_IFF_C

end Fefferman.ConcreteReal
