import QuasiFeffermanB.EnergyPhysicalContinuity
set_option pp.universes false
set_option pp.explicit false

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.energyH0PhysicalMap_apply"
#check @QuasiFeffermanB.energyH0PhysicalMap_apply
#eval IO.println "TYPE_END:QuasiFeffermanB.energyH0PhysicalMap_apply"
#print axioms QuasiFeffermanB.energyH0PhysicalMap_apply

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.ENERGY_PHYSICAL_L2_WEAK_CONTINUITY"
#check @QuasiFeffermanB.ENERGY_PHYSICAL_L2_WEAK_CONTINUITY
#eval IO.println "TYPE_END:QuasiFeffermanB.ENERGY_PHYSICAL_L2_WEAK_CONTINUITY"
#print axioms QuasiFeffermanB.ENERGY_PHYSICAL_L2_WEAK_CONTINUITY

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.ENERGY_PERIODIC_WEAK_CONTINUITY"
#check @QuasiFeffermanB.ENERGY_PERIODIC_WEAK_CONTINUITY
#eval IO.println "TYPE_END:QuasiFeffermanB.ENERGY_PERIODIC_WEAK_CONTINUITY"
#print axioms QuasiFeffermanB.ENERGY_PERIODIC_WEAK_CONTINUITY
