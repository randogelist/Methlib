import QuasiFeffermanB.LHExistence
set_option pp.universes false
set_option pp.explicit false

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.galerkin_H1_time_energy_bound"
#check @QuasiFeffermanB.galerkin_H1_time_energy_bound
#eval IO.println "TYPE_END:QuasiFeffermanB.galerkin_H1_time_energy_bound"
#print axioms QuasiFeffermanB.galerkin_H1_time_energy_bound

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.galerkin_critical_zero_norm_sq"
#check @QuasiFeffermanB.galerkin_critical_zero_norm_sq
#eval IO.println "TYPE_END:QuasiFeffermanB.galerkin_critical_zero_norm_sq"
#print axioms QuasiFeffermanB.galerkin_critical_zero_norm_sq

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.ENERGY_GALERKIN_H0_COEFFICIENT_LIMIT"
#check @QuasiFeffermanB.ENERGY_GALERKIN_H0_COEFFICIENT_LIMIT
#eval IO.println "TYPE_END:QuasiFeffermanB.ENERGY_GALERKIN_H0_COEFFICIENT_LIMIT"
#print axioms QuasiFeffermanB.ENERGY_GALERKIN_H0_COEFFICIENT_LIMIT

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.ENERGY_GALERKIN_L2H0_SUBSEQUENCE"
#check @QuasiFeffermanB.ENERGY_GALERKIN_L2H0_SUBSEQUENCE
#eval IO.println "TYPE_END:QuasiFeffermanB.ENERGY_GALERKIN_L2H0_SUBSEQUENCE"
#print axioms QuasiFeffermanB.ENERGY_GALERKIN_L2H0_SUBSEQUENCE
