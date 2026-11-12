import SingularityDisprovement.SINGULARITY_DISPROVEMENT_REGULARITY_CHAIN

open SingularClosure SingularityDisprovement
open scoped ENNReal

example (ν ε : ℝ) (hν : 0 < ν) (hε : 0 < ε) :
    (∀ a : CriticalSobolev 1, Premise ν ε a → Reg ν a) ∧
    (∃ a : CriticalSobolev 1, Premise ν ε a) ∧
    (∃ a : CriticalSobolev 1,
      CriticalSigmaZero a ∧ 0 < ‖a‖ ∧ ‖a‖ < ε ∧
      calibratedScore ν a < 2 ∧ densityEssSup a = ⊤ ∧ Reg ν a) :=
  SINGULARITY_DISPROVEMENT_REGULARITY_CHAIN ν ε hν hε

#eval IO.println "EXACT_TYPE_PASS:SingularityDisprovement.SINGULARITY_DISPROVEMENT_REGULARITY_CHAIN"
#check @SingularityDisprovement.SINGULARITY_DISPROVEMENT_REGULARITY_CHAIN
#print axioms SingularityDisprovement.SINGULARITY_DISPROVEMENT_REGULARITY_CHAIN

