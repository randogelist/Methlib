import QuasiFeffermanB.CaloricGalerkinMajorant
set_option pp.universes false
set_option pp.explicit false

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.finiteModeConvolution_nonneg"
#check @QuasiFeffermanB.finiteModeConvolution_nonneg
#eval IO.println "TYPE_END:QuasiFeffermanB.finiteModeConvolution_nonneg"
#print axioms QuasiFeffermanB.finiteModeConvolution_nonneg

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.FINITE_MODE_CONVOLUTION_SUM_LE_CHI0_SQUARE"
#check @QuasiFeffermanB.FINITE_MODE_CONVOLUTION_SUM_LE_CHI0_SQUARE
#eval IO.println "TYPE_END:QuasiFeffermanB.FINITE_MODE_CONVOLUTION_SUM_LE_CHI0_SQUARE"
#print axioms QuasiFeffermanB.FINITE_MODE_CONVOLUTION_SUM_LE_CHI0_SQUARE

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.GALERKIN_MODE_CONVOLUTION_CONTINUOUS"
#check @QuasiFeffermanB.GALERKIN_MODE_CONVOLUTION_CONTINUOUS
#eval IO.println "TYPE_END:QuasiFeffermanB.GALERKIN_MODE_CONVOLUTION_CONTINUOUS"
#print axioms QuasiFeffermanB.GALERKIN_MODE_CONVOLUTION_CONTINUOUS

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.GALERKIN_MODE_DUHAMEL_NORM"
#check @QuasiFeffermanB.GALERKIN_MODE_DUHAMEL_NORM
#eval IO.println "TYPE_END:QuasiFeffermanB.GALERKIN_MODE_DUHAMEL_NORM"
#print axioms QuasiFeffermanB.GALERKIN_MODE_DUHAMEL_NORM

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.GALERKIN_MODE_CALORIC_MAJORANT"
#check @QuasiFeffermanB.GALERKIN_MODE_CALORIC_MAJORANT
#eval IO.println "TYPE_END:QuasiFeffermanB.GALERKIN_MODE_CALORIC_MAJORANT"
#print axioms QuasiFeffermanB.GALERKIN_MODE_CALORIC_MAJORANT

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.GALERKIN_CHI0_BUDGET_OF_SHARP_MULTIPLIER_AND_HEAT"
#check @QuasiFeffermanB.GALERKIN_CHI0_BUDGET_OF_SHARP_MULTIPLIER_AND_HEAT
#eval IO.println "TYPE_END:QuasiFeffermanB.GALERKIN_CHI0_BUDGET_OF_SHARP_MULTIPLIER_AND_HEAT"
#print axioms QuasiFeffermanB.GALERKIN_CHI0_BUDGET_OF_SHARP_MULTIPLIER_AND_HEAT

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.FINITE_HEAT_L2_ON_INTERVAL_LE"
#check @QuasiFeffermanB.FINITE_HEAT_L2_ON_INTERVAL_LE
#eval IO.println "TYPE_END:QuasiFeffermanB.FINITE_HEAT_L2_ON_INTERVAL_LE"
#print axioms QuasiFeffermanB.FINITE_HEAT_L2_ON_INTERVAL_LE

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.GALERKIN_CHI0_BUDGET_OF_CALORIC_QUADRATIC"
#check @QuasiFeffermanB.GALERKIN_CHI0_BUDGET_OF_CALORIC_QUADRATIC
#eval IO.println "TYPE_END:QuasiFeffermanB.GALERKIN_CHI0_BUDGET_OF_CALORIC_QUADRATIC"
#print axioms QuasiFeffermanB.GALERKIN_CHI0_BUDGET_OF_CALORIC_QUADRATIC
