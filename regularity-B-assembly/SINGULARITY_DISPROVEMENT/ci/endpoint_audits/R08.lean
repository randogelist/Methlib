import SingularityDisprovement.DyadicUnbounded

open SingularClosure SingularityDisprovement

example (ν : ℝ) (hν : 0 < ν) : EssUnbounded (dyadicSeed ν) :=
  dyadicSeed_essUnbounded ν hν

#eval IO.println "EXACT_TYPE_PASS:SingularityDisprovement.dyadicSeed_essUnbounded"
#check @SingularityDisprovement.dyadicSeed_essUnbounded
#print axioms SingularityDisprovement.dyadicSeed_essUnbounded
