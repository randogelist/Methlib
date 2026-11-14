import QuasiFeffermanB.TailRegularity
set_option pp.universes false
set_option pp.explicit false

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.positive_timeDerivative_translate"
#check @QuasiFeffermanB.positive_timeDerivative_translate
#eval IO.println "TYPE_END:QuasiFeffermanB.positive_timeDerivative_translate"
#print axioms QuasiFeffermanB.positive_timeDerivative_translate

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.CLASSICAL_TAIL_OF_POSITIVE_SMOOTH_NSE"
#check @QuasiFeffermanB.CLASSICAL_TAIL_OF_POSITIVE_SMOOTH_NSE
#eval IO.println "TYPE_END:QuasiFeffermanB.CLASSICAL_TAIL_OF_POSITIVE_SMOOTH_NSE"
#print axioms QuasiFeffermanB.CLASSICAL_TAIL_OF_POSITIVE_SMOOTH_NSE

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.HAS_SMOOTH_TAIL_OF_POSITIVE_REFERENCE"
#check @QuasiFeffermanB.HAS_SMOOTH_TAIL_OF_POSITIVE_REFERENCE
#eval IO.println "TYPE_END:QuasiFeffermanB.HAS_SMOOTH_TAIL_OF_POSITIVE_REFERENCE"
#print axioms QuasiFeffermanB.HAS_SMOOTH_TAIL_OF_POSITIVE_REFERENCE

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.HAS_SMOOTH_TAIL_OF_POSITIVE_FLOW"
#check @QuasiFeffermanB.HAS_SMOOTH_TAIL_OF_POSITIVE_FLOW
#eval IO.println "TYPE_END:QuasiFeffermanB.HAS_SMOOTH_TAIL_OF_POSITIVE_FLOW"
#print axioms QuasiFeffermanB.HAS_SMOOTH_TAIL_OF_POSITIVE_FLOW
