import QuasiFeffermanB.EnergyGlobalLimit
set_option pp.universes false
set_option pp.explicit false

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.ENERGY_GALERKIN_GLOBAL_LIMIT"
#check @QuasiFeffermanB.ENERGY_GALERKIN_GLOBAL_LIMIT
#eval IO.println "TYPE_END:QuasiFeffermanB.ENERGY_GALERKIN_GLOBAL_LIMIT"
#print axioms QuasiFeffermanB.ENERGY_GALERKIN_GLOBAL_LIMIT

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.energy_modal_limit_constraints"
#check @QuasiFeffermanB.energy_modal_limit_constraints
#eval IO.println "TYPE_END:QuasiFeffermanB.energy_modal_limit_constraints"
#print axioms QuasiFeffermanB.energy_modal_limit_constraints

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.energy_modal_limit_H1_representative"
#check @QuasiFeffermanB.energy_modal_limit_H1_representative
#eval IO.println "TYPE_END:QuasiFeffermanB.energy_modal_limit_H1_representative"
#print axioms QuasiFeffermanB.energy_modal_limit_H1_representative
