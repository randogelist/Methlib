import SingularityDisprovement.Admission

open SingularClosure SingularityDisprovement
open scoped BigOperators

example (a : CriticalSobolev 1) (ha : CriticalSigmaZero a) :
    (‖a‖ ^ 2 = ∑' ki : FourierIndex,
      criticalFrequencyWeight ki.1 * Complex.normSq (criticalCoeff 1 a ki.1 ki.2)) ∧
    (‖physicalL2 a‖ ^ 2 = ∑' ki : FourierIndex,
      Complex.normSq (criticalCoeff 1 a ki.1 ki.2)) ∧
    datumFourierCoeff (physicalL2 a : Field) = criticalCoeff 1 a :=
  NATIVE_ENERGY_REALIZATION a ha

#eval IO.println "EXACT_TYPE_PASS:SingularityDisprovement.NATIVE_ENERGY_REALIZATION"
#check @SingularityDisprovement.NATIVE_ENERGY_REALIZATION
#print axioms SingularityDisprovement.NATIVE_ENERGY_REALIZATION

