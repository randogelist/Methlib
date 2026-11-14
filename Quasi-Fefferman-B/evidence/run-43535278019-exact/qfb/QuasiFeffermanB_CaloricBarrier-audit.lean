import QuasiFeffermanB.CaloricBarrier
set_option pp.universes false
set_option pp.explicit false

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.CONTINUOUS_QUADRATIC_BARRIER"
#check @QuasiFeffermanB.CONTINUOUS_QUADRATIC_BARRIER
#eval IO.println "TYPE_END:QuasiFeffermanB.CONTINUOUS_QUADRATIC_BARRIER"
#print axioms QuasiFeffermanB.CONTINUOUS_QUADRATIC_BARRIER

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.QUADRATIC_BARRIER_LT_TWO_HEAT_BUDGET"
#check @QuasiFeffermanB.QUADRATIC_BARRIER_LT_TWO_HEAT_BUDGET
#eval IO.println "TYPE_END:QuasiFeffermanB.QUADRATIC_BARRIER_LT_TWO_HEAT_BUDGET"
#print axioms QuasiFeffermanB.QUADRATIC_BARRIER_LT_TWO_HEAT_BUDGET

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.QUADRATIC_BARRIER_ZERO_HEAT_BUDGET"
#check @QuasiFeffermanB.QUADRATIC_BARRIER_ZERO_HEAT_BUDGET
#eval IO.println "TYPE_END:QuasiFeffermanB.QUADRATIC_BARRIER_ZERO_HEAT_BUDGET"
#print axioms QuasiFeffermanB.QUADRATIC_BARRIER_ZERO_HEAT_BUDGET

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.QUADRATIC_BARRIER_LE_TWO_HEAT_BUDGET"
#check @QuasiFeffermanB.QUADRATIC_BARRIER_LE_TWO_HEAT_BUDGET
#eval IO.println "TYPE_END:QuasiFeffermanB.QUADRATIC_BARRIER_LE_TWO_HEAT_BUDGET"
#print axioms QuasiFeffermanB.QUADRATIC_BARRIER_LE_TWO_HEAT_BUDGET

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.QUADRATIC_BARRIER_SQUARE_BUDGET"
#check @QuasiFeffermanB.QUADRATIC_BARRIER_SQUARE_BUDGET
#eval IO.println "TYPE_END:QuasiFeffermanB.QUADRATIC_BARRIER_SQUARE_BUDGET"
#print axioms QuasiFeffermanB.QUADRATIC_BARRIER_SQUARE_BUDGET
