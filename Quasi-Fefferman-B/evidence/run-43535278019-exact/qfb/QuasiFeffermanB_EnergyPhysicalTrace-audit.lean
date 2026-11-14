import QuasiFeffermanB.EnergyPhysicalTrace
set_option pp.universes false
set_option pp.explicit false

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.energyPhysicalVelocityL2_initial"
#check @QuasiFeffermanB.energyPhysicalVelocityL2_initial
#eval IO.println "TYPE_END:QuasiFeffermanB.energyPhysicalVelocityL2_initial"
#print axioms QuasiFeffermanB.energyPhysicalVelocityL2_initial

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.energyPeriodicVelocity_initial"
#check @QuasiFeffermanB.energyPeriodicVelocity_initial
#eval IO.println "TYPE_END:QuasiFeffermanB.energyPeriodicVelocity_initial"
#print axioms QuasiFeffermanB.energyPeriodicVelocity_initial

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.energyPhysical_initial_norm"
#check @QuasiFeffermanB.energyPhysical_initial_norm
#eval IO.println "TYPE_END:QuasiFeffermanB.energyPhysical_initial_norm"
#print axioms QuasiFeffermanB.energyPhysical_initial_norm

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.ENERGY_PHYSICAL_STRONG_INITIAL_TRACE"
#check @QuasiFeffermanB.ENERGY_PHYSICAL_STRONG_INITIAL_TRACE
#eval IO.println "TYPE_END:QuasiFeffermanB.ENERGY_PHYSICAL_STRONG_INITIAL_TRACE"
#print axioms QuasiFeffermanB.ENERGY_PHYSICAL_STRONG_INITIAL_TRACE
