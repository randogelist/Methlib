import ConcreteABCDUnifiedClosure

/-! Fefferman B. The endpoint and joint equivalences have no construction premises. -/

namespace Fefferman.ConcreteReal

example : PeriodicZeroForceGlobalRegularity → B realAnalysis :=
  periodicZeroForceGlobalRegularity_implies_B

example : PeriodicZeroForceGlobalRegularity ↔ B realAnalysis :=
  PERIODIC_ZERO_FORCE_GLOBAL_REGULARITY_IFF_B

example : MasterABSemantic ↔ (A realAnalysis ∧ B realAnalysis) :=
  masterABSemantic_iff_A_and_B

end Fefferman.ConcreteReal
