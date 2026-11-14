import QuasiFeffermanB.EnergyTransportContinuity
set_option pp.universes false
set_option pp.explicit false

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.energyMatrixAction_coe"
#check @QuasiFeffermanB.energyMatrixAction_coe
#eval IO.println "TYPE_END:QuasiFeffermanB.energyMatrixAction_coe"
#print axioms QuasiFeffermanB.energyMatrixAction_coe

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.energyTestMatrix_coe"
#check @QuasiFeffermanB.energyTestMatrix_coe
#eval IO.println "TYPE_END:QuasiFeffermanB.energyTestMatrix_coe"
#print axioms QuasiFeffermanB.energyTestMatrix_coe

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.energyWeakTransport_eq_L2_inner"
#check @QuasiFeffermanB.energyWeakTransport_eq_L2_inner
#eval IO.println "TYPE_END:QuasiFeffermanB.energyWeakTransport_eq_L2_inner"
#print axioms QuasiFeffermanB.energyWeakTransport_eq_L2_inner

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.energyMatrixQuadratic_continuous"
#check @QuasiFeffermanB.energyMatrixQuadratic_continuous
#eval IO.println "TYPE_END:QuasiFeffermanB.energyMatrixQuadratic_continuous"
#print axioms QuasiFeffermanB.energyMatrixQuadratic_continuous

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.energyWeakTransport_L2_tendsto"
#check @QuasiFeffermanB.energyWeakTransport_L2_tendsto
#eval IO.println "TYPE_END:QuasiFeffermanB.energyWeakTransport_L2_tendsto"
#print axioms QuasiFeffermanB.energyWeakTransport_L2_tendsto

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.energyMatrixQuadratic_bound"
#check @QuasiFeffermanB.energyMatrixQuadratic_bound
#eval IO.println "TYPE_END:QuasiFeffermanB.energyMatrixQuadratic_bound"
#print axioms QuasiFeffermanB.energyMatrixQuadratic_bound

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.energyWeakTransport_L2_bound"
#check @QuasiFeffermanB.energyWeakTransport_L2_bound
#eval IO.println "TYPE_END:QuasiFeffermanB.energyWeakTransport_L2_bound"
#print axioms QuasiFeffermanB.energyWeakTransport_L2_bound

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.energyWeakTransport_congr_ae"
#check @QuasiFeffermanB.energyWeakTransport_congr_ae
#eval IO.println "TYPE_END:QuasiFeffermanB.energyWeakTransport_congr_ae"
#print axioms QuasiFeffermanB.energyWeakTransport_congr_ae
