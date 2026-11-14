import QuasiFeffermanB.PhysicalH1Admission
set_option pp.universes false
set_option pp.explicit false

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.meanZero_sobolevCutoff_sum"
#check @QuasiFeffermanB.meanZero_sobolevCutoff_sum
#eval IO.println "TYPE_END:QuasiFeffermanB.meanZero_sobolevCutoff_sum"
#print axioms QuasiFeffermanB.meanZero_sobolevCutoff_sum

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.physicalH1_weighted_finite_bound"
#check @QuasiFeffermanB.physicalH1_weighted_finite_bound
#eval IO.println "TYPE_END:QuasiFeffermanB.physicalH1_weighted_finite_bound"
#print axioms QuasiFeffermanB.physicalH1_weighted_finite_bound

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.physicalH1_mem_sobolevTwo"
#check @QuasiFeffermanB.physicalH1_mem_sobolevTwo
#eval IO.println "TYPE_END:QuasiFeffermanB.physicalH1_mem_sobolevTwo"
#print axioms QuasiFeffermanB.physicalH1_mem_sobolevTwo

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.physicalH1SobolevDatum_lower_half"
#check @QuasiFeffermanB.physicalH1SobolevDatum_lower_half
#eval IO.println "TYPE_END:QuasiFeffermanB.physicalH1SobolevDatum_lower_half"
#print axioms QuasiFeffermanB.physicalH1SobolevDatum_lower_half

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.physicalH1SobolevDatum_half_norm_sq"
#check @QuasiFeffermanB.physicalH1SobolevDatum_half_norm_sq
#eval IO.println "TYPE_END:QuasiFeffermanB.physicalH1SobolevDatum_half_norm_sq"
#print axioms QuasiFeffermanB.physicalH1SobolevDatum_half_norm_sq

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.physicalH1SobolevDatum_physicalL2"
#check @QuasiFeffermanB.physicalH1SobolevDatum_physicalL2
#eval IO.println "TYPE_END:QuasiFeffermanB.physicalH1SobolevDatum_physicalL2"
#print axioms QuasiFeffermanB.physicalH1SobolevDatum_physicalL2
