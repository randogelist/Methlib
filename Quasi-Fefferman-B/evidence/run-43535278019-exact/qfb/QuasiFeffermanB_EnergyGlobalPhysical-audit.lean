import QuasiFeffermanB.EnergyGlobalPhysical
set_option pp.universes false
set_option pp.explicit false

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.energyGlobalH1State_eq"
#check @QuasiFeffermanB.energyGlobalH1State_eq
#eval IO.println "TYPE_END:QuasiFeffermanB.energyGlobalH1State_eq"
#print axioms QuasiFeffermanB.energyGlobalH1State_eq

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.energyGlobalH1State_ae_eq"
#check @QuasiFeffermanB.energyGlobalH1State_ae_eq
#eval IO.println "TYPE_END:QuasiFeffermanB.energyGlobalH1State_ae_eq"
#print axioms QuasiFeffermanB.energyGlobalH1State_ae_eq

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.energyGlobalH1State_memLp"
#check @QuasiFeffermanB.energyGlobalH1State_memLp
#eval IO.println "TYPE_END:QuasiFeffermanB.energyGlobalH1State_memLp"
#print axioms QuasiFeffermanB.energyGlobalH1State_memLp

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.energyGlobalGradient_memLp"
#check @QuasiFeffermanB.energyGlobalGradient_memLp
#eval IO.println "TYPE_END:QuasiFeffermanB.energyGlobalGradient_memLp"
#print axioms QuasiFeffermanB.energyGlobalGradient_memLp

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.energyPhysicalVelocity_eq_H1"
#check @QuasiFeffermanB.energyPhysicalVelocity_eq_H1
#eval IO.println "TYPE_END:QuasiFeffermanB.energyPhysicalVelocity_eq_H1"
#print axioms QuasiFeffermanB.energyPhysicalVelocity_eq_H1

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.energyGlobalPhysical_spatial_H1"
#check @QuasiFeffermanB.energyGlobalPhysical_spatial_H1
#eval IO.println "TYPE_END:QuasiFeffermanB.energyGlobalPhysical_spatial_H1"
#print axioms QuasiFeffermanB.energyGlobalPhysical_spatial_H1

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.energyGlobalGradient_energy_ae"
#check @QuasiFeffermanB.energyGlobalGradient_energy_ae
#eval IO.println "TYPE_END:QuasiFeffermanB.energyGlobalGradient_energy_ae"
#print axioms QuasiFeffermanB.energyGlobalGradient_energy_ae

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.energyGlobalGradient_energy_integrable"
#check @QuasiFeffermanB.energyGlobalGradient_energy_integrable
#eval IO.println "TYPE_END:QuasiFeffermanB.energyGlobalGradient_energy_integrable"
#print axioms QuasiFeffermanB.energyGlobalGradient_energy_integrable
