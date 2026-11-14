import QuasiFeffermanB.EnergyTimeCompactness
set_option pp.universes false
set_option pp.explicit false

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.energyTimeH0L2_norm_sq"
#check @QuasiFeffermanB.energyTimeH0L2_norm_sq
#eval IO.println "TYPE_END:QuasiFeffermanB.energyTimeH0L2_norm_sq"
#print axioms QuasiFeffermanB.energyTimeH0L2_norm_sq

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.energy_H0_tail_sq"
#check @QuasiFeffermanB.energy_H0_tail_sq
#eval IO.println "TYPE_END:QuasiFeffermanB.energy_H0_tail_sq"
#print axioms QuasiFeffermanB.energy_H0_tail_sq

#eval IO.println "TYPE_BEGIN:SingularClosure.GalerkinSolution.energy_H0_time_tail"
#check @SingularClosure.GalerkinSolution.energy_H0_time_tail
#eval IO.println "TYPE_END:SingularClosure.GalerkinSolution.energy_H0_time_tail"
#print axioms SingularClosure.GalerkinSolution.energy_H0_time_tail

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.energyGalerkin_H0_time_difference_bound"
#check @QuasiFeffermanB.energyGalerkin_H0_time_difference_bound
#eval IO.println "TYPE_END:QuasiFeffermanB.energyGalerkin_H0_time_difference_bound"
#print axioms QuasiFeffermanB.energyGalerkin_H0_time_difference_bound

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.energyTimeH0L2_sub_norm_sq"
#check @QuasiFeffermanB.energyTimeH0L2_sub_norm_sq
#eval IO.println "TYPE_END:QuasiFeffermanB.energyTimeH0L2_sub_norm_sq"
#print axioms QuasiFeffermanB.energyTimeH0L2_sub_norm_sq

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.ENERGY_GALERKIN_L2H0_LIMIT_OF_COEFFICIENT_UNIFORM"
#check @QuasiFeffermanB.ENERGY_GALERKIN_L2H0_LIMIT_OF_COEFFICIENT_UNIFORM
#eval IO.println "TYPE_END:QuasiFeffermanB.ENERGY_GALERKIN_L2H0_LIMIT_OF_COEFFICIENT_UNIFORM"
#print axioms QuasiFeffermanB.ENERGY_GALERKIN_L2H0_LIMIT_OF_COEFFICIENT_UNIFORM
