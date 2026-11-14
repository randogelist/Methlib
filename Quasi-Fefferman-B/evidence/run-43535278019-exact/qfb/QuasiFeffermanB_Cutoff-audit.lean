import QuasiFeffermanB.Cutoff
set_option pp.universes false
set_option pp.explicit false

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.CUTOFF_NONNEG"
#check @QuasiFeffermanB.CUTOFF_NONNEG
#eval IO.println "TYPE_END:QuasiFeffermanB.CUTOFF_NONNEG"
#print axioms QuasiFeffermanB.CUTOFF_NONNEG

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.CUTOFF_ZERO"
#check @QuasiFeffermanB.CUTOFF_ZERO
#eval IO.println "TYPE_END:QuasiFeffermanB.CUTOFF_ZERO"
#print axioms QuasiFeffermanB.CUTOFF_ZERO

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.CUTOFF_POS"
#check @QuasiFeffermanB.CUTOFF_POS
#eval IO.println "TYPE_END:QuasiFeffermanB.CUTOFF_POS"
#print axioms QuasiFeffermanB.CUTOFF_POS

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.SAFE_CUTOFF_GT"
#check @QuasiFeffermanB.SAFE_CUTOFF_GT
#eval IO.println "TYPE_END:QuasiFeffermanB.SAFE_CUTOFF_GT"
#print axioms QuasiFeffermanB.SAFE_CUTOFF_GT

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.ENERGY_SLICE_CUTOFF"
#check @QuasiFeffermanB.ENERGY_SLICE_CUTOFF
#eval IO.println "TYPE_END:QuasiFeffermanB.ENERGY_SLICE_CUTOFF"
#print axioms QuasiFeffermanB.ENERGY_SLICE_CUTOFF
