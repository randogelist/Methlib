import ConcreteABCDUnifiedClosure

/-! Fefferman A. The endpoint and joint equivalences have no construction premises. -/

namespace Fefferman.ConcreteReal

example : WholeSpaceZeroForceGlobalRegularity → A realAnalysis :=
  wholeSpaceZeroForceGlobalRegularity_implies_A

example : WholeSpaceZeroForceGlobalRegularity ↔ A realAnalysis :=
  WHOLESPACE_ZERO_FORCE_GLOBAL_REGULARITY_IFF_A

example : MasterABSemantic ↔ (A realAnalysis ∧ B realAnalysis) :=
  masterABSemantic_iff_A_and_B

end Fefferman.ConcreteReal
