import QuasiFeffermanB.FourierEnergy
set_option pp.universes false
set_option pp.explicit false

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.physicalEnergy_eq_toLp_norm_sq"
#check @QuasiFeffermanB.physicalEnergy_eq_toLp_norm_sq
#eval IO.println "TYPE_END:QuasiFeffermanB.physicalEnergy_eq_toLp_norm_sq"
#print axioms QuasiFeffermanB.physicalEnergy_eq_toLp_norm_sq

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.physicalEnergy_tendsto_of_L2"
#check @QuasiFeffermanB.physicalEnergy_tendsto_of_L2
#eval IO.println "TYPE_END:QuasiFeffermanB.physicalEnergy_tendsto_of_L2"
#print axioms QuasiFeffermanB.physicalEnergy_tendsto_of_L2

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.physicalEnergy_compCLM_tendsto_of_L2"
#check @QuasiFeffermanB.physicalEnergy_compCLM_tendsto_of_L2
#eval IO.println "TYPE_END:QuasiFeffermanB.physicalEnergy_compCLM_tendsto_of_L2"
#print axioms QuasiFeffermanB.physicalEnergy_compCLM_tendsto_of_L2

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.datumFourierCoeff_tendsto_of_L2"
#check @QuasiFeffermanB.datumFourierCoeff_tendsto_of_L2
#eval IO.println "TYPE_END:QuasiFeffermanB.datumFourierCoeff_tendsto_of_L2"
#print axioms QuasiFeffermanB.datumFourierCoeff_tendsto_of_L2

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.physicalH1_cutoff_bounds"
#check @QuasiFeffermanB.physicalH1_cutoff_bounds
#eval IO.println "TYPE_END:QuasiFeffermanB.physicalH1_cutoff_bounds"
#print axioms QuasiFeffermanB.physicalH1_cutoff_bounds

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.criticalEnergy_midpoint"
#check @QuasiFeffermanB.criticalEnergy_midpoint
#eval IO.println "TYPE_END:QuasiFeffermanB.criticalEnergy_midpoint"
#print axioms QuasiFeffermanB.criticalEnergy_midpoint

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.physicalH1_cutoff_midpoint"
#check @QuasiFeffermanB.physicalH1_cutoff_midpoint
#eval IO.println "TYPE_END:QuasiFeffermanB.physicalH1_cutoff_midpoint"
#print axioms QuasiFeffermanB.physicalH1_cutoff_midpoint

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.physicalHalfEnergyTerm_nonneg"
#check @QuasiFeffermanB.physicalHalfEnergyTerm_nonneg
#eval IO.println "TYPE_END:QuasiFeffermanB.physicalHalfEnergyTerm_nonneg"
#print axioms QuasiFeffermanB.physicalHalfEnergyTerm_nonneg

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.physicalHalfEnergy_cutoff"
#check @QuasiFeffermanB.physicalHalfEnergy_cutoff
#eval IO.println "TYPE_END:QuasiFeffermanB.physicalHalfEnergy_cutoff"
#print axioms QuasiFeffermanB.physicalHalfEnergy_cutoff

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.physicalH1_halfEnergy_le"
#check @QuasiFeffermanB.physicalH1_halfEnergy_le
#eval IO.println "TYPE_END:QuasiFeffermanB.physicalH1_halfEnergy_le"
#print axioms QuasiFeffermanB.physicalH1_halfEnergy_le

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.physicalH1_halfEnergy_ne_top"
#check @QuasiFeffermanB.physicalH1_halfEnergy_ne_top
#eval IO.println "TYPE_END:QuasiFeffermanB.physicalH1_halfEnergy_ne_top"
#print axioms QuasiFeffermanB.physicalH1_halfEnergy_ne_top

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.physicalH1_halfEnergy_midpoint"
#check @QuasiFeffermanB.physicalH1_halfEnergy_midpoint
#eval IO.println "TYPE_END:QuasiFeffermanB.physicalH1_halfEnergy_midpoint"
#print axioms QuasiFeffermanB.physicalH1_halfEnergy_midpoint

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.physicalHalfEnergy_toReal_eq_tsum"
#check @QuasiFeffermanB.physicalHalfEnergy_toReal_eq_tsum
#eval IO.println "TYPE_END:QuasiFeffermanB.physicalHalfEnergy_toReal_eq_tsum"
#print axioms QuasiFeffermanB.physicalHalfEnergy_toReal_eq_tsum

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.physicalH1_halfEnergy_summable"
#check @QuasiFeffermanB.physicalH1_halfEnergy_summable
#eval IO.println "TYPE_END:QuasiFeffermanB.physicalH1_halfEnergy_summable"
#print axioms QuasiFeffermanB.physicalH1_halfEnergy_summable

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.physicalHalfEnergyTerm_of_meanZero"
#check @QuasiFeffermanB.physicalHalfEnergyTerm_of_meanZero
#eval IO.println "TYPE_END:QuasiFeffermanB.physicalHalfEnergyTerm_of_meanZero"
#print axioms QuasiFeffermanB.physicalHalfEnergyTerm_of_meanZero

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.physicalH1_mem_halfSobolev"
#check @QuasiFeffermanB.physicalH1_mem_halfSobolev
#eval IO.println "TYPE_END:QuasiFeffermanB.physicalH1_mem_halfSobolev"
#print axioms QuasiFeffermanB.physicalH1_mem_halfSobolev

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.physicalH1HalfDatum_norm_sq"
#check @QuasiFeffermanB.physicalH1HalfDatum_norm_sq
#eval IO.println "TYPE_END:QuasiFeffermanB.physicalH1HalfDatum_norm_sq"
#print axioms QuasiFeffermanB.physicalH1HalfDatum_norm_sq

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.physicalHalfEnergy_aemeasurable"
#check @QuasiFeffermanB.physicalHalfEnergy_aemeasurable
#eval IO.println "TYPE_END:QuasiFeffermanB.physicalHalfEnergy_aemeasurable"
#print axioms QuasiFeffermanB.physicalHalfEnergy_aemeasurable
