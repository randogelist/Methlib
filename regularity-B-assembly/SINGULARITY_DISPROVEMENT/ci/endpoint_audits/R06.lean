import SingularityDisprovement.DyadicNorms

open SingularClosure SingularityDisprovement

example (ν : ℝ) (hν : 0 < ν) :
    CriticalSigmaZero (dyadicSeed ν) ∧
    0 < ‖dyadicSeed ν‖ ∧
    ‖physicalL2 (dyadicSeed ν)‖ ^ 2 = ν ^ 2 * dyadicR / 8 ∧
    ‖dyadicSeed ν‖ ^ 2 = Real.pi * ν ^ 2 * dyadicS / 8 :=
  DYADIC_CRITICAL_DATUM ν hν

#eval IO.println "EXACT_TYPE_PASS:SingularityDisprovement.DYADIC_CRITICAL_DATUM"
#check @SingularityDisprovement.DYADIC_CRITICAL_DATUM
#print axioms SingularityDisprovement.DYADIC_CRITICAL_DATUM
