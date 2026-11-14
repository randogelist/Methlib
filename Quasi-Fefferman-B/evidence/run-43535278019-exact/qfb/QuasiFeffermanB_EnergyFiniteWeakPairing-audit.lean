import QuasiFeffermanB.EnergyFiniteWeakPairing
set_option pp.universes false
set_option pp.explicit false

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.energy_galerkin_mode_pairing"
#check @QuasiFeffermanB.energy_galerkin_mode_pairing
#eval IO.println "TYPE_END:QuasiFeffermanB.energy_galerkin_mode_pairing"
#print axioms QuasiFeffermanB.energy_galerkin_mode_pairing

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.ENERGY_FINITE_GALERKIN_WEAK_PAIRING"
#check @QuasiFeffermanB.ENERGY_FINITE_GALERKIN_WEAK_PAIRING
#eval IO.println "TYPE_END:QuasiFeffermanB.ENERGY_FINITE_GALERKIN_WEAK_PAIRING"
#print axioms QuasiFeffermanB.ENERGY_FINITE_GALERKIN_WEAK_PAIRING

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.energyGalerkin_finite_test_pairing"
#check @QuasiFeffermanB.energyGalerkin_finite_test_pairing
#eval IO.println "TYPE_END:QuasiFeffermanB.energyGalerkin_finite_test_pairing"
#print axioms QuasiFeffermanB.energyGalerkin_finite_test_pairing
