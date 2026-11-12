import SingularityDisprovement.Scaling

open SingularClosure SingularityDisprovement

example (ν ε : ℝ) (hν : 0 < ν) (hε : 0 < ε)
    (b : CriticalSobolev 1) (hb : CriticalSigmaZero b) (hbpos : 0 < ‖b‖) :
    ∃ m : ℕ, 1 ≤ m ∧
      0 < ‖((1 / 2 : ℝ) ^ m) • b‖ ∧
      ‖((1 / 2 : ℝ) ^ m) • b‖ < ε ∧
      calibratedScore ν (((1 / 2 : ℝ) ^ m) • b) < 1 :=
  SMALL_POSITIVE_DYADIC_SCALE_EXISTS ν ε hν hε b hb hbpos

#eval IO.println "EXACT_TYPE_PASS:SingularityDisprovement.SMALL_POSITIVE_DYADIC_SCALE_EXISTS"
#check @SingularityDisprovement.SMALL_POSITIVE_DYADIC_SCALE_EXISTS
#print axioms SingularityDisprovement.SMALL_POSITIVE_DYADIC_SCALE_EXISTS

