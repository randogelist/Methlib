import QuasiFeffermanB.TimeTranslate
set_option pp.universes false
set_option pp.explicit false

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.restartTimeClamp_pos"
#check @QuasiFeffermanB.restartTimeClamp_pos
#eval IO.println "TYPE_END:QuasiFeffermanB.restartTimeClamp_pos"
#print axioms QuasiFeffermanB.restartTimeClamp_pos

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.restartTimeClamp_contDiff"
#check @QuasiFeffermanB.restartTimeClamp_contDiff
#eval IO.println "TYPE_END:QuasiFeffermanB.restartTimeClamp_contDiff"
#print axioms QuasiFeffermanB.restartTimeClamp_contDiff

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.restartTimeClamp_eq"
#check @QuasiFeffermanB.restartTimeClamp_eq
#eval IO.println "TYPE_END:QuasiFeffermanB.restartTimeClamp_eq"
#print axioms QuasiFeffermanB.restartTimeClamp_eq

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.restartTimeClamp_hasDerivAt"
#check @QuasiFeffermanB.restartTimeClamp_hasDerivAt
#eval IO.println "TYPE_END:QuasiFeffermanB.restartTimeClamp_hasDerivAt"
#print axioms QuasiFeffermanB.restartTimeClamp_hasDerivAt

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.restartTest_is_test"
#check @QuasiFeffermanB.restartTest_is_test
#eval IO.println "TYPE_END:QuasiFeffermanB.restartTest_is_test"
#print axioms QuasiFeffermanB.restartTest_is_test

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.restartTest_eq"
#check @QuasiFeffermanB.restartTest_eq
#eval IO.println "TYPE_END:QuasiFeffermanB.restartTest_eq"
#print axioms QuasiFeffermanB.restartTest_eq

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.restartTest_timeDerivative"
#check @QuasiFeffermanB.restartTest_timeDerivative
#eval IO.println "TYPE_END:QuasiFeffermanB.restartTest_timeDerivative"
#print axioms QuasiFeffermanB.restartTest_timeDerivative

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.timeTranslate_integrated_momentum"
#check @QuasiFeffermanB.timeTranslate_integrated_momentum
#eval IO.println "TYPE_END:QuasiFeffermanB.timeTranslate_integrated_momentum"
#print axioms QuasiFeffermanB.timeTranslate_integrated_momentum

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.timeTranslate_measurePreserving_Ioc"
#check @QuasiFeffermanB.timeTranslate_measurePreserving_Ioc
#eval IO.println "TYPE_END:QuasiFeffermanB.timeTranslate_measurePreserving_Ioc"
#print axioms QuasiFeffermanB.timeTranslate_measurePreserving_Ioc

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.timeTranslate_memLp_Ioc"
#check @QuasiFeffermanB.timeTranslate_memLp_Ioc
#eval IO.println "TYPE_END:QuasiFeffermanB.timeTranslate_memLp_Ioc"
#print axioms QuasiFeffermanB.timeTranslate_memLp_Ioc

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.timeTranslate_ae_Ioc"
#check @QuasiFeffermanB.timeTranslate_ae_Ioc
#eval IO.println "TYPE_END:QuasiFeffermanB.timeTranslate_ae_Ioc"
#print axioms QuasiFeffermanB.timeTranslate_ae_Ioc
