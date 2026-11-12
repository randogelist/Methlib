import SingularityDisprovement.SINGULARITY_DISPROVEMENT_REGULARITY_CHAIN

open SingularClosure SingularityDisprovement

example (ν ε : ℝ) (hν : 0 < ν) (hε : 0 < ε) :
    ∃ a : CriticalSobolev 1, Premise ν ε a :=
  ADMISSION_NONEMPTY ν ε hν hε

#eval IO.println "EXACT_TYPE_PASS:SingularityDisprovement.ADMISSION_NONEMPTY"
#check @SingularityDisprovement.ADMISSION_NONEMPTY
#print axioms SingularityDisprovement.ADMISSION_NONEMPTY

