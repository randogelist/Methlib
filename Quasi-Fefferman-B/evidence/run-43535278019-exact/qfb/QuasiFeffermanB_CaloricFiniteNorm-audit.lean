import QuasiFeffermanB.CaloricFiniteNorm
set_option pp.universes false
set_option pp.explicit false

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.finiteTimeL2_nonneg"
#check @QuasiFeffermanB.finiteTimeL2_nonneg
#eval IO.println "TYPE_END:QuasiFeffermanB.finiteTimeL2_nonneg"
#print axioms QuasiFeffermanB.finiteTimeL2_nonneg

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.finiteTimeL2_sq"
#check @QuasiFeffermanB.finiteTimeL2_sq
#eval IO.println "TYPE_END:QuasiFeffermanB.finiteTimeL2_sq"
#print axioms QuasiFeffermanB.finiteTimeL2_sq

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.caloric_continuous_memLp_two"
#check @QuasiFeffermanB.caloric_continuous_memLp_two
#eval IO.println "TYPE_END:QuasiFeffermanB.caloric_continuous_memLp_two"
#print axioms QuasiFeffermanB.caloric_continuous_memLp_two

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.finiteTimeL2_cauchy"
#check @QuasiFeffermanB.finiteTimeL2_cauchy
#eval IO.println "TYPE_END:QuasiFeffermanB.finiteTimeL2_cauchy"
#print axioms QuasiFeffermanB.finiteTimeL2_cauchy

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.finiteTimeL2_mono"
#check @QuasiFeffermanB.finiteTimeL2_mono
#eval IO.println "TYPE_END:QuasiFeffermanB.finiteTimeL2_mono"
#print axioms QuasiFeffermanB.finiteTimeL2_mono

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.finiteTimeL2_add_le"
#check @QuasiFeffermanB.finiteTimeL2_add_le
#eval IO.println "TYPE_END:QuasiFeffermanB.finiteTimeL2_add_le"
#print axioms QuasiFeffermanB.finiteTimeL2_add_le

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.finiteTimeL2_const_mul"
#check @QuasiFeffermanB.finiteTimeL2_const_mul
#eval IO.println "TYPE_END:QuasiFeffermanB.finiteTimeL2_const_mul"
#print axioms QuasiFeffermanB.finiteTimeL2_const_mul

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.finiteTimeL2_sum_le"
#check @QuasiFeffermanB.finiteTimeL2_sum_le
#eval IO.println "TYPE_END:QuasiFeffermanB.finiteTimeL2_sum_le"
#print axioms QuasiFeffermanB.finiteTimeL2_sum_le

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.CALORIC_VOLTERRA_L2_BOUND"
#check @QuasiFeffermanB.CALORIC_VOLTERRA_L2_BOUND
#eval IO.println "TYPE_END:QuasiFeffermanB.CALORIC_VOLTERRA_L2_BOUND"
#print axioms QuasiFeffermanB.CALORIC_VOLTERRA_L2_BOUND

#eval IO.println "TYPE_BEGIN:QuasiFeffermanB.FINITE_NONNEGATIVE_CONVOLUTION_L1"
#check @QuasiFeffermanB.FINITE_NONNEGATIVE_CONVOLUTION_L1
#eval IO.println "TYPE_END:QuasiFeffermanB.FINITE_NONNEGATIVE_CONVOLUTION_L1"
#print axioms QuasiFeffermanB.FINITE_NONNEGATIVE_CONVOLUTION_L1
