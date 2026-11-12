import SingularityDisprovement.Admission

open SingularClosure SingularityDisprovement
open scoped BigOperators

example (ν : ℝ) (hν : 0 < ν) (a : CriticalSobolev 1) (ha : CriticalSigmaZero a)
    (hscore : calibratedScore ν a < 2) : Reg ν a :=
  ADMISSION_IMPLIES_REGULARITY ν hν a ha hscore

#eval IO.println "EXACT_TYPE_PASS:SingularityDisprovement.ADMISSION_IMPLIES_REGULARITY"
#check @SingularityDisprovement.ADMISSION_IMPLIES_REGULARITY
#print axioms SingularityDisprovement.ADMISSION_IMPLIES_REGULARITY

