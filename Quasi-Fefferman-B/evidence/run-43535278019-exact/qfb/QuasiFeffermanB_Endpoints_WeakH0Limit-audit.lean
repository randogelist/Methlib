import QuasiFeffermanB.Endpoints.WeakH0Limit
set_option pp.universes false
set_option pp.explicit false

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.ENERGY_LP_WEAK_TENDSTO"
#check @QuasiFeffermanB.ENERGY_LP_WEAK_TENDSTO
#eval IO.println "TYPE_END:QuasiFeffermanB.ENERGY_LP_WEAK_TENDSTO"
#print axioms QuasiFeffermanB.ENERGY_LP_WEAK_TENDSTO

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.ENERGY_H0_WEAK_TENDSTO"
#check @QuasiFeffermanB.ENERGY_H0_WEAK_TENDSTO
#eval IO.println "TYPE_END:QuasiFeffermanB.ENERGY_H0_WEAK_TENDSTO"
#print axioms QuasiFeffermanB.ENERGY_H0_WEAK_TENDSTO

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.ENERGY_H0_LIMIT_NORM_LE"
#check @QuasiFeffermanB.ENERGY_H0_LIMIT_NORM_LE
#eval IO.println "TYPE_END:QuasiFeffermanB.ENERGY_H0_LIMIT_NORM_LE"
#print axioms QuasiFeffermanB.ENERGY_H0_LIMIT_NORM_LE

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.ENERGY_PHYSICAL_L2_WEAK_TENDSTO"
#check @QuasiFeffermanB.ENERGY_PHYSICAL_L2_WEAK_TENDSTO
#eval IO.println "TYPE_END:QuasiFeffermanB.ENERGY_PHYSICAL_L2_WEAK_TENDSTO"
#print axioms QuasiFeffermanB.ENERGY_PHYSICAL_L2_WEAK_TENDSTO

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.energy_galerkin_physical_L2"
#check @QuasiFeffermanB.energy_galerkin_physical_L2
#eval IO.println "TYPE_END:QuasiFeffermanB.energy_galerkin_physical_L2"
#print axioms QuasiFeffermanB.energy_galerkin_physical_L2

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.ENERGY_GALERKIN_PHYSICAL_PAIRING_TENDSTO"
#check @QuasiFeffermanB.ENERGY_GALERKIN_PHYSICAL_PAIRING_TENDSTO
#eval IO.println "TYPE_END:QuasiFeffermanB.ENERGY_GALERKIN_PHYSICAL_PAIRING_TENDSTO"
#print axioms QuasiFeffermanB.ENERGY_GALERKIN_PHYSICAL_PAIRING_TENDSTO
