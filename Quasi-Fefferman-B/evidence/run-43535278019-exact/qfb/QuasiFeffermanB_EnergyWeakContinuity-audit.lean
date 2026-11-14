import QuasiFeffermanB.EnergyWeakContinuity
set_option pp.universes false
set_option pp.explicit false

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.energy_lp_inner_projection"
#check @QuasiFeffermanB.energy_lp_inner_projection
#eval IO.println "TYPE_END:QuasiFeffermanB.energy_lp_inner_projection"
#print axioms QuasiFeffermanB.energy_lp_inner_projection

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.energy_lp_projection_tendsto"
#check @QuasiFeffermanB.energy_lp_projection_tendsto
#eval IO.println "TYPE_END:QuasiFeffermanB.energy_lp_projection_tendsto"
#print axioms QuasiFeffermanB.energy_lp_projection_tendsto

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.ENERGY_LP_WEAK_CONTINUITY"
#check @QuasiFeffermanB.ENERGY_LP_WEAK_CONTINUITY
#eval IO.println "TYPE_END:QuasiFeffermanB.ENERGY_LP_WEAK_CONTINUITY"
#print axioms QuasiFeffermanB.ENERGY_LP_WEAK_CONTINUITY

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.ENERGY_H0_WEAK_CONTINUITY"
#check @QuasiFeffermanB.ENERGY_H0_WEAK_CONTINUITY
#eval IO.println "TYPE_END:QuasiFeffermanB.ENERGY_H0_WEAK_CONTINUITY"
#print axioms QuasiFeffermanB.ENERGY_H0_WEAK_CONTINUITY

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.energy_complex_strong_tendsto_of_inner_and_norm_bound"
#check @QuasiFeffermanB.energy_complex_strong_tendsto_of_inner_and_norm_bound
#eval IO.println "TYPE_END:QuasiFeffermanB.energy_complex_strong_tendsto_of_inner_and_norm_bound"
#print axioms QuasiFeffermanB.energy_complex_strong_tendsto_of_inner_and_norm_bound

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.ENERGY_H0_STRONG_INITIAL_TRACE"
#check @QuasiFeffermanB.ENERGY_H0_STRONG_INITIAL_TRACE
#eval IO.println "TYPE_END:QuasiFeffermanB.ENERGY_H0_STRONG_INITIAL_TRACE"
#print axioms QuasiFeffermanB.ENERGY_H0_STRONG_INITIAL_TRACE
