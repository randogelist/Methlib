import QuasiFeffermanB.MeanPreservation
set_option pp.universes false
set_option pp.explicit false

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.physical_inner_congr_left_ae"
#check @QuasiFeffermanB.physical_inner_congr_left_ae
#eval IO.println "TYPE_END:QuasiFeffermanB.physical_inner_congr_left_ae"
#print axioms QuasiFeffermanB.physical_inner_congr_left_ae

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.constant_positive_solenoidal_test"
#check @QuasiFeffermanB.constant_positive_solenoidal_test
#eval IO.println "TYPE_END:QuasiFeffermanB.constant_positive_solenoidal_test"
#print axioms QuasiFeffermanB.constant_positive_solenoidal_test

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.constant_weak_momentum_integrand"
#check @QuasiFeffermanB.constant_weak_momentum_integrand
#eval IO.println "TYPE_END:QuasiFeffermanB.constant_weak_momentum_integrand"
#print axioms QuasiFeffermanB.constant_weak_momentum_integrand

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.LH_CONSTANT_PAIRING_PRESERVED"
#check @QuasiFeffermanB.LH_CONSTANT_PAIRING_PRESERVED
#eval IO.println "TYPE_END:QuasiFeffermanB.LH_CONSTANT_PAIRING_PRESERVED"
#print axioms QuasiFeffermanB.LH_CONSTANT_PAIRING_PRESERVED

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.LH_POSITIVE_TRACE_ENERGY_SIGMA_ZERO"
#check @QuasiFeffermanB.LH_POSITIVE_TRACE_ENERGY_SIGMA_ZERO
#eval IO.println "TYPE_END:QuasiFeffermanB.LH_POSITIVE_TRACE_ENERGY_SIGMA_ZERO"
#print axioms QuasiFeffermanB.LH_POSITIVE_TRACE_ENERGY_SIGMA_ZERO
