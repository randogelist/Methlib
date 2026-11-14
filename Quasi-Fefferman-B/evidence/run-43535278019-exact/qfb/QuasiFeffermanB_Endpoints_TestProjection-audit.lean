import QuasiFeffermanB.Endpoints.TestProjection
set_option pp.universes false
set_option pp.explicit false

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.energy_sobolevCutoffModes_tendsto"
#check @QuasiFeffermanB.energy_sobolevCutoffModes_tendsto
#eval IO.println "TYPE_END:QuasiFeffermanB.energy_sobolevCutoffModes_tendsto"
#print axioms QuasiFeffermanB.energy_sobolevCutoffModes_tendsto

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.energy_smooth_datumFourier_reconstruction"
#check @QuasiFeffermanB.energy_smooth_datumFourier_reconstruction
#eval IO.println "TYPE_END:QuasiFeffermanB.energy_smooth_datumFourier_reconstruction"
#print axioms QuasiFeffermanB.energy_smooth_datumFourier_reconstruction

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.energy_smooth_derivative_fourierSeries"
#check @QuasiFeffermanB.energy_smooth_derivative_fourierSeries
#eval IO.println "TYPE_END:QuasiFeffermanB.energy_smooth_derivative_fourierSeries"
#print axioms QuasiFeffermanB.energy_smooth_derivative_fourierSeries

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.energy_finite_derivative_fourierSum"
#check @QuasiFeffermanB.energy_finite_derivative_fourierSum
#eval IO.println "TYPE_END:QuasiFeffermanB.energy_finite_derivative_fourierSum"
#print axioms QuasiFeffermanB.energy_finite_derivative_fourierSum

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.energy_vector_norm_le_three"
#check @QuasiFeffermanB.energy_vector_norm_le_three
#eval IO.println "TYPE_END:QuasiFeffermanB.energy_vector_norm_le_three"
#print axioms QuasiFeffermanB.energy_vector_norm_le_three

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.energy_operator_norm_le_nine"
#check @QuasiFeffermanB.energy_operator_norm_le_nine
#eval IO.println "TYPE_END:QuasiFeffermanB.energy_operator_norm_le_nine"
#print axioms QuasiFeffermanB.energy_operator_norm_le_nine

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.energyTest_derivative_entries_uniform"
#check @QuasiFeffermanB.energyTest_derivative_entries_uniform
#eval IO.println "TYPE_END:QuasiFeffermanB.energyTest_derivative_entries_uniform"
#print axioms QuasiFeffermanB.energyTest_derivative_entries_uniform

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.ENERGY_TEST_DERIVATIVE_CUTOFF_UNIFORM"
#check @QuasiFeffermanB.ENERGY_TEST_DERIVATIVE_CUTOFF_UNIFORM
#eval IO.println "TYPE_END:QuasiFeffermanB.ENERGY_TEST_DERIVATIVE_CUTOFF_UNIFORM"
#print axioms QuasiFeffermanB.ENERGY_TEST_DERIVATIVE_CUTOFF_UNIFORM

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.ENERGY_TEST_DERIVATIVE_CUTOFF_BOUND"
#check @QuasiFeffermanB.ENERGY_TEST_DERIVATIVE_CUTOFF_BOUND
#eval IO.println "TYPE_END:QuasiFeffermanB.ENERGY_TEST_DERIVATIVE_CUTOFF_BOUND"
#print axioms QuasiFeffermanB.ENERGY_TEST_DERIVATIVE_CUTOFF_BOUND
