import QuasiFeffermanB.PhysicalFourierL2
set_option pp.universes false
set_option pp.explicit false

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.torusDatumRepresentative_measurePreserving"
#check @QuasiFeffermanB.torusDatumRepresentative_measurePreserving
#eval IO.println "TYPE_END:QuasiFeffermanB.torusDatumRepresentative_measurePreserving"
#print axioms QuasiFeffermanB.torusDatumRepresentative_measurePreserving

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.rough_torusDatumComponent_memLp"
#check @QuasiFeffermanB.rough_torusDatumComponent_memLp
#eval IO.println "TYPE_END:QuasiFeffermanB.rough_torusDatumComponent_memLp"
#print axioms QuasiFeffermanB.rough_torusDatumComponent_memLp

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.physicalTorusComponentL2_coeff"
#check @QuasiFeffermanB.physicalTorusComponentL2_coeff
#eval IO.println "TYPE_END:QuasiFeffermanB.physicalTorusComponentL2_coeff"
#print axioms QuasiFeffermanB.physicalTorusComponentL2_coeff

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.physicalTorusComponentL2_norm_sq"
#check @QuasiFeffermanB.physicalTorusComponentL2_norm_sq
#eval IO.println "TYPE_END:QuasiFeffermanB.physicalTorusComponentL2_norm_sq"
#print axioms QuasiFeffermanB.physicalTorusComponentL2_norm_sq

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.physicalTorusComponentL2_sum_norm_sq"
#check @QuasiFeffermanB.physicalTorusComponentL2_sum_norm_sq
#eval IO.println "TYPE_END:QuasiFeffermanB.physicalTorusComponentL2_sum_norm_sq"
#print axioms QuasiFeffermanB.physicalTorusComponentL2_sum_norm_sq

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.physicalL2_coefficientEnergy_le"
#check @QuasiFeffermanB.physicalL2_coefficientEnergy_le
#eval IO.println "TYPE_END:QuasiFeffermanB.physicalL2_coefficientEnergy_le"
#print axioms QuasiFeffermanB.physicalL2_coefficientEnergy_le

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.physicalL2_fourier_mem"
#check @QuasiFeffermanB.physicalL2_fourier_mem
#eval IO.println "TYPE_END:QuasiFeffermanB.physicalL2_fourier_mem"
#print axioms QuasiFeffermanB.physicalL2_fourier_mem

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.physicalFourierSequence_component"
#check @QuasiFeffermanB.physicalFourierSequence_component
#eval IO.println "TYPE_END:QuasiFeffermanB.physicalFourierSequence_component"
#print axioms QuasiFeffermanB.physicalFourierSequence_component

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.physicalFourierSequence_norm_sq"
#check @QuasiFeffermanB.physicalFourierSequence_norm_sq
#eval IO.println "TYPE_END:QuasiFeffermanB.physicalFourierSequence_norm_sq"
#print axioms QuasiFeffermanB.physicalFourierSequence_norm_sq

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.physical_datumFourierCoeff_sub"
#check @QuasiFeffermanB.physical_datumFourierCoeff_sub
#eval IO.println "TYPE_END:QuasiFeffermanB.physical_datumFourierCoeff_sub"
#print axioms QuasiFeffermanB.physical_datumFourierCoeff_sub

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.physicalL2_fourier_injective"
#check @QuasiFeffermanB.physicalL2_fourier_injective
#eval IO.println "TYPE_END:QuasiFeffermanB.physicalL2_fourier_injective"
#print axioms QuasiFeffermanB.physicalL2_fourier_injective

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.physicalH1HalfDatum_physicalL2"
#check @QuasiFeffermanB.physicalH1HalfDatum_physicalL2
#eval IO.println "TYPE_END:QuasiFeffermanB.physicalH1HalfDatum_physicalL2"
#print axioms QuasiFeffermanB.physicalH1HalfDatum_physicalL2

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.physicalL2SobolevDatum_norm"
#check @QuasiFeffermanB.physicalL2SobolevDatum_norm
#eval IO.println "TYPE_END:QuasiFeffermanB.physicalL2SobolevDatum_norm"
#print axioms QuasiFeffermanB.physicalL2SobolevDatum_norm

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.physicalL2SobolevDatum_sub"
#check @QuasiFeffermanB.physicalL2SobolevDatum_sub
#eval IO.println "TYPE_END:QuasiFeffermanB.physicalL2SobolevDatum_sub"
#print axioms QuasiFeffermanB.physicalL2SobolevDatum_sub

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.physicalL2SobolevDatum_finite"
#check @QuasiFeffermanB.physicalL2SobolevDatum_finite
#eval IO.println "TYPE_END:QuasiFeffermanB.physicalL2SobolevDatum_finite"
#print axioms QuasiFeffermanB.physicalL2SobolevDatum_finite

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.physicalL2_cutoff_tendsto"
#check @QuasiFeffermanB.physicalL2_cutoff_tendsto
#eval IO.println "TYPE_END:QuasiFeffermanB.physicalL2_cutoff_tendsto"
#print axioms QuasiFeffermanB.physicalL2_cutoff_tendsto

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.physicalL2_cutoff_eLpNorm_tendsto"
#check @QuasiFeffermanB.physicalL2_cutoff_eLpNorm_tendsto
#eval IO.println "TYPE_END:QuasiFeffermanB.physicalL2_cutoff_eLpNorm_tendsto"
#print axioms QuasiFeffermanB.physicalL2_cutoff_eLpNorm_tendsto

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.zeroSobolevPhysicalL2_continuous"
#check @QuasiFeffermanB.zeroSobolevPhysicalL2_continuous
#eval IO.println "TYPE_END:QuasiFeffermanB.zeroSobolevPhysicalL2_continuous"
#print axioms QuasiFeffermanB.zeroSobolevPhysicalL2_continuous

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.zeroSobolevPhysicalL2_finite"
#check @QuasiFeffermanB.zeroSobolevPhysicalL2_finite
#eval IO.println "TYPE_END:QuasiFeffermanB.zeroSobolevPhysicalL2_finite"
#print axioms QuasiFeffermanB.zeroSobolevPhysicalL2_finite

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.zeroSobolevPhysicalL2_fourierCoeff"
#check @QuasiFeffermanB.zeroSobolevPhysicalL2_fourierCoeff
#eval IO.println "TYPE_END:QuasiFeffermanB.zeroSobolevPhysicalL2_fourierCoeff"
#print axioms QuasiFeffermanB.zeroSobolevPhysicalL2_fourierCoeff

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.zeroSobolevPhysicalL2_norm"
#check @QuasiFeffermanB.zeroSobolevPhysicalL2_norm
#eval IO.println "TYPE_END:QuasiFeffermanB.zeroSobolevPhysicalL2_norm"
#print axioms QuasiFeffermanB.zeroSobolevPhysicalL2_norm

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.torusSobolevH0_physical_fourierCoeff"
#check @QuasiFeffermanB.torusSobolevH0_physical_fourierCoeff
#eval IO.println "TYPE_END:QuasiFeffermanB.torusSobolevH0_physical_fourierCoeff"
#print axioms QuasiFeffermanB.torusSobolevH0_physical_fourierCoeff

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.torusSobolevH0_physical_norm"
#check @QuasiFeffermanB.torusSobolevH0_physical_norm
#eval IO.println "TYPE_END:QuasiFeffermanB.torusSobolevH0_physical_norm"
#print axioms QuasiFeffermanB.torusSobolevH0_physical_norm
