import QuasiFeffermanB.EnergyLimitEnergy
set_option pp.universes false
set_option pp.explicit false

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.energy_modal_eventually_lower"
#check @QuasiFeffermanB.energy_modal_eventually_lower
#eval IO.println "TYPE_END:QuasiFeffermanB.energy_modal_eventually_lower"
#print axioms QuasiFeffermanB.energy_modal_eventually_lower

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.energy_modal_lintegral_le_of_eventual_budget"
#check @QuasiFeffermanB.energy_modal_lintegral_le_of_eventual_budget
#eval IO.println "TYPE_END:QuasiFeffermanB.energy_modal_lintegral_le_of_eventual_budget"
#print axioms QuasiFeffermanB.energy_modal_lintegral_le_of_eventual_budget

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.ENERGY_MODAL_INTERVAL_BUDGET_LIMIT"
#check @QuasiFeffermanB.ENERGY_MODAL_INTERVAL_BUDGET_LIMIT
#eval IO.println "TYPE_END:QuasiFeffermanB.ENERGY_MODAL_INTERVAL_BUDGET_LIMIT"
#print axioms QuasiFeffermanB.ENERGY_MODAL_INTERVAL_BUDGET_LIMIT

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.GALERKIN_INTERVAL_ENERGY_IDENTITY"
#check @QuasiFeffermanB.GALERKIN_INTERVAL_ENERGY_IDENTITY
#eval IO.println "TYPE_END:QuasiFeffermanB.GALERKIN_INTERVAL_ENERGY_IDENTITY"
#print axioms QuasiFeffermanB.GALERKIN_INTERVAL_ENERGY_IDENTITY

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.ENERGY_GALERKIN_INTERVAL_LIMIT"
#check @QuasiFeffermanB.ENERGY_GALERKIN_INTERVAL_LIMIT
#eval IO.println "TYPE_END:QuasiFeffermanB.ENERGY_GALERKIN_INTERVAL_LIMIT"
#print axioms QuasiFeffermanB.ENERGY_GALERKIN_INTERVAL_LIMIT
