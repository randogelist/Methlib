import QuasiFeffermanB.EnergyDatumApproximation
set_option pp.universes false
set_option pp.explicit false

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.energyDatumGalerkinFamily_initial"
#check @QuasiFeffermanB.energyDatumGalerkinFamily_initial
#eval IO.println "TYPE_END:QuasiFeffermanB.energyDatumGalerkinFamily_initial"
#print axioms QuasiFeffermanB.energyDatumGalerkinFamily_initial

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.energyDatumGalerkinFamily_energy_initial"
#check @QuasiFeffermanB.energyDatumGalerkinFamily_energy_initial
#eval IO.println "TYPE_END:QuasiFeffermanB.energyDatumGalerkinFamily_energy_initial"
#print axioms QuasiFeffermanB.energyDatumGalerkinFamily_energy_initial

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.ENERGY_DATUM_GALERKIN_COMPACTNESS"
#check @QuasiFeffermanB.ENERGY_DATUM_GALERKIN_COMPACTNESS
#eval IO.println "TYPE_END:QuasiFeffermanB.ENERGY_DATUM_GALERKIN_COMPACTNESS"
#print axioms QuasiFeffermanB.ENERGY_DATUM_GALERKIN_COMPACTNESS
