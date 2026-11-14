import QuasiFeffermanB.CaloricGalerkinBudget
set_option pp.universes false
set_option pp.explicit false

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.REAL_SCALAR_DUHAMEL"
#check @QuasiFeffermanB.REAL_SCALAR_DUHAMEL
#eval IO.println "TYPE_END:QuasiFeffermanB.REAL_SCALAR_DUHAMEL"
#print axioms QuasiFeffermanB.REAL_SCALAR_DUHAMEL

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.complexVec_sum_units"
#check @QuasiFeffermanB.complexVec_sum_units
#eval IO.println "TYPE_END:QuasiFeffermanB.complexVec_sum_units"
#print axioms QuasiFeffermanB.complexVec_sum_units

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.GALERKIN_COMPLEX_MODE_CONTINUOUS"
#check @QuasiFeffermanB.GALERKIN_COMPLEX_MODE_CONTINUOUS
#eval IO.println "TYPE_END:QuasiFeffermanB.GALERKIN_COMPLEX_MODE_CONTINUOUS"
#print axioms QuasiFeffermanB.GALERKIN_COMPLEX_MODE_CONTINUOUS

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.GALERKIN_COMPLEX_MODE_HAS_DERIV"
#check @QuasiFeffermanB.GALERKIN_COMPLEX_MODE_HAS_DERIV
#eval IO.println "TYPE_END:QuasiFeffermanB.GALERKIN_COMPLEX_MODE_HAS_DERIV"
#print axioms QuasiFeffermanB.GALERKIN_COMPLEX_MODE_HAS_DERIV

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.GALERKIN_COMPLEX_FORCING_CONTINUOUS"
#check @QuasiFeffermanB.GALERKIN_COMPLEX_FORCING_CONTINUOUS
#eval IO.println "TYPE_END:QuasiFeffermanB.GALERKIN_COMPLEX_FORCING_CONTINUOUS"
#print axioms QuasiFeffermanB.GALERKIN_COMPLEX_FORCING_CONTINUOUS

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.GALERKIN_MODE_DUHAMEL"
#check @QuasiFeffermanB.GALERKIN_MODE_DUHAMEL
#eval IO.println "TYPE_END:QuasiFeffermanB.GALERKIN_MODE_DUHAMEL"
#print axioms QuasiFeffermanB.GALERKIN_MODE_DUHAMEL
