import SingularityDisprovement.DyadicScale

open SingularClosure SingularityDisprovement

example (ν ε : ℝ) (hν : 0 < ν) (hε : 0 < ε) :
    ∃ m : ℕ, 1 ≤ m ∧
      0 < ‖((1 / 2 : ℝ) ^ m) • dyadicSeed ν‖ ∧
      ‖((1 / 2 : ℝ) ^ m) • dyadicSeed ν‖ < ε ∧
      calibratedScore ν (((1 / 2 : ℝ) ^ m) • dyadicSeed ν) < 1 :=
  DYADIC_ADMITTED_SCALE ν ε hν hε

#eval IO.println "EXACT_TYPE_PASS:SingularityDisprovement.DYADIC_ADMITTED_SCALE"
#check @SingularityDisprovement.DYADIC_ADMITTED_SCALE
#print axioms SingularityDisprovement.DYADIC_ADMITTED_SCALE

