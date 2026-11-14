import QuasiFeffermanB.CaloricConvolution
set_option pp.universes false
set_option pp.explicit false

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.caloric_primitive_continuousOn"
#check @QuasiFeffermanB.caloric_primitive_continuousOn
#eval IO.println "TYPE_END:QuasiFeffermanB.caloric_primitive_continuousOn"
#print axioms QuasiFeffermanB.caloric_primitive_continuousOn

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.caloric_primitive_hasDerivAt"
#check @QuasiFeffermanB.caloric_primitive_hasDerivAt
#eval IO.println "TYPE_END:QuasiFeffermanB.caloric_primitive_hasDerivAt"
#print axioms QuasiFeffermanB.caloric_primitive_hasDerivAt

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.caloricVolterra_kernel"
#check @QuasiFeffermanB.caloricVolterra_kernel
#eval IO.println "TYPE_END:QuasiFeffermanB.caloricVolterra_kernel"
#print axioms QuasiFeffermanB.caloricVolterra_kernel

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.caloricVolterra_continuousOn"
#check @QuasiFeffermanB.caloricVolterra_continuousOn
#eval IO.println "TYPE_END:QuasiFeffermanB.caloricVolterra_continuousOn"
#print axioms QuasiFeffermanB.caloricVolterra_continuousOn

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.caloricVolterra_hasDerivAt"
#check @QuasiFeffermanB.caloricVolterra_hasDerivAt
#eval IO.println "TYPE_END:QuasiFeffermanB.caloricVolterra_hasDerivAt"
#print axioms QuasiFeffermanB.caloricVolterra_hasDerivAt

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.caloricVolterra_nonneg_le_primitive"
#check @QuasiFeffermanB.caloricVolterra_nonneg_le_primitive
#eval IO.println "TYPE_END:QuasiFeffermanB.caloricVolterra_nonneg_le_primitive"
#print axioms QuasiFeffermanB.caloricVolterra_nonneg_le_primitive

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.CALORIC_VOLTERRA_L2_SQUARE_BOUND"
#check @QuasiFeffermanB.CALORIC_VOLTERRA_L2_SQUARE_BOUND
#eval IO.println "TYPE_END:QuasiFeffermanB.CALORIC_VOLTERRA_L2_SQUARE_BOUND"
#print axioms QuasiFeffermanB.CALORIC_VOLTERRA_L2_SQUARE_BOUND
