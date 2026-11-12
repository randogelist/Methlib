import SingularityDisprovement.Admission

open SingularClosure SingularityDisprovement
open scoped BigOperators

example (ν : ℝ) (hν : 0 < ν) (a : CriticalSobolev 1) (ha : CriticalSigmaZero a) :
    calibrationGamma * ‖a‖ ^ 2 ≤ 2 * ν ^ 2 * shiftedEnergy ν a ∧
    2 * ν ^ 2 * shiftedEnergy ν a ≤ ‖a‖ ^ 2 :=
  SHIFTED_ENERGY_COERCIVITY ν hν a ha

#eval IO.println "EXACT_TYPE_PASS:SingularityDisprovement.SHIFTED_ENERGY_COERCIVITY"
#check @SingularityDisprovement.SHIFTED_ENERGY_COERCIVITY
#print axioms SingularityDisprovement.SHIFTED_ENERGY_COERCIVITY

