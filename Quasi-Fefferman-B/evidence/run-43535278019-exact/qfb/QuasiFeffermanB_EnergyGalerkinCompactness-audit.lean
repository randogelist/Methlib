import QuasiFeffermanB.EnergyGalerkinCompactness
set_option pp.universes false
set_option pp.explicit false

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.energyModeTransportBound_nonneg"
#check @QuasiFeffermanB.energyModeTransportBound_nonneg
#eval IO.println "TYPE_END:QuasiFeffermanB.energyModeTransportBound_nonneg"
#print axioms QuasiFeffermanB.energyModeTransportBound_nonneg

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.energyModeTransport_norm_le"
#check @QuasiFeffermanB.energyModeTransport_norm_le
#eval IO.println "TYPE_END:QuasiFeffermanB.energyModeTransport_norm_le"
#print axioms QuasiFeffermanB.energyModeTransport_norm_le

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.energyModeRhsBound_nonneg"
#check @QuasiFeffermanB.energyModeRhsBound_nonneg
#eval IO.println "TYPE_END:QuasiFeffermanB.energyModeRhsBound_nonneg"
#print axioms QuasiFeffermanB.energyModeRhsBound_nonneg

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.fullFourierRhs_energy_bound"
#check @QuasiFeffermanB.fullFourierRhs_energy_bound
#eval IO.println "TYPE_END:QuasiFeffermanB.fullFourierRhs_energy_bound"
#print axioms QuasiFeffermanB.fullFourierRhs_energy_bound

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.galerkin_H0_norm_sq"
#check @QuasiFeffermanB.galerkin_H0_norm_sq
#eval IO.println "TYPE_END:QuasiFeffermanB.galerkin_H0_norm_sq"
#print axioms QuasiFeffermanB.galerkin_H0_norm_sq

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.galerkin_H0_energy_bound"
#check @QuasiFeffermanB.galerkin_H0_energy_bound
#eval IO.println "TYPE_END:QuasiFeffermanB.galerkin_H0_energy_bound"
#print axioms QuasiFeffermanB.galerkin_H0_energy_bound

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.galerkin_energy_coefficient_modulus"
#check @QuasiFeffermanB.galerkin_energy_coefficient_modulus
#eval IO.println "TYPE_END:QuasiFeffermanB.galerkin_energy_coefficient_modulus"
#print axioms QuasiFeffermanB.galerkin_energy_coefficient_modulus

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.ENERGY_GALERKIN_COEFFICIENT_SUBSEQUENCE"
#check @QuasiFeffermanB.ENERGY_GALERKIN_COEFFICIENT_SUBSEQUENCE
#eval IO.println "TYPE_END:QuasiFeffermanB.ENERGY_GALERKIN_COEFFICIENT_SUBSEQUENCE"
#print axioms QuasiFeffermanB.ENERGY_GALERKIN_COEFFICIENT_SUBSEQUENCE
