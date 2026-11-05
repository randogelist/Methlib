import FeffermanB

namespace Fefferman.ConcreteReal

example : ABCDPhysicalPort →
    (A realAnalysis ∧ B realAnalysis ∧ C realAnalysis ∧ D realAnalysis) :=
  ABCD_PHYSICAL_PORT_IFF_FEFFERMAN_ABCD.mp

end Fefferman.ConcreteReal

#print axioms Fefferman.ConcreteReal.masterABSemantic_iff_A_and_B
#print axioms Fefferman.ConcreteReal.masterCDSemantic_iff_C_and_D
#print axioms Fefferman.ConcreteReal.abcdPhysicalEndpoints_iff_ABCD
#print axioms Fefferman.ConcreteReal.ABCD_PHYSICAL_PORT_IFF_FEFFERMAN_ABCD
#print axioms Fefferman.ConcreteReal.MASTER_CD_SEMANTIC_IFF_C_AND_D
#print axioms Fefferman.ConcreteReal.FEFFERMAN_ABCD_A_TIER_UNIFIED_CLOSURE_ATLAS
#print axioms Fefferman.ConcreteReal.periodicZeroForceGlobalRegularity_implies_B
#print axioms Fefferman.ConcreteReal.PERIODIC_ZERO_FORCE_GLOBAL_REGULARITY_IFF_B
