import QuasiFeffermanB.CaloricFourierBridge
set_option pp.universes false
set_option pp.explicit false

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.complexVecNorm_finset_sum_le"
#check @QuasiFeffermanB.complexVecNorm_finset_sum_le
#eval IO.println "TYPE_END:QuasiFeffermanB.complexVecNorm_finset_sum_le"
#print axioms QuasiFeffermanB.complexVecNorm_finset_sum_le

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.coefficientTransport_frequencyDot"
#check @QuasiFeffermanB.coefficientTransport_frequencyDot
#eval IO.println "TYPE_END:QuasiFeffermanB.coefficientTransport_frequencyDot"
#print axioms QuasiFeffermanB.coefficientTransport_frequencyDot

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.finite_convolution_swap"
#check @QuasiFeffermanB.finite_convolution_swap
#eval IO.println "TYPE_END:QuasiFeffermanB.finite_convolution_swap"
#print axioms QuasiFeffermanB.finite_convolution_swap

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.coefficientTransport_symmetric"
#check @QuasiFeffermanB.coefficientTransport_symmetric
#eval IO.println "TYPE_END:QuasiFeffermanB.coefficientTransport_symmetric"
#print axioms QuasiFeffermanB.coefficientTransport_symmetric

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.coefficientLeray_transport_symmetric"
#check @QuasiFeffermanB.coefficientLeray_transport_symmetric
#eval IO.println "TYPE_END:QuasiFeffermanB.coefficientLeray_transport_symmetric"
#print axioms QuasiFeffermanB.coefficientLeray_transport_symmetric
