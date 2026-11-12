import SingularityDisprovement.Admission

open SingularClosure SingularityDisprovement
open scoped BigOperators

example (ν : ℝ) (hν : 0 < ν) (a : CriticalSobolev 1) (ha : CriticalSigmaZero a)
    (hscore : calibratedScore ν a < 2) :
    criticalNonlinearConstant * ‖a‖ < ν :=
  FIRST_STAGE_IMPLIES_NATIVE_SMALL ν hν a ha hscore

example : 0 < calibrationCap := calibrationCap_pos
example : stageZeroBudget = 2 ∧ stageZeroBudget < Real.pi := stageZeroBudget_eq_two_lt_pi

#eval IO.println "EXACT_TYPE_PASS:SingularityDisprovement.FIRST_STAGE_IMPLIES_NATIVE_SMALL"
#check @SingularityDisprovement.FIRST_STAGE_IMPLIES_NATIVE_SMALL
#print axioms SingularityDisprovement.FIRST_STAGE_IMPLIES_NATIVE_SMALL

