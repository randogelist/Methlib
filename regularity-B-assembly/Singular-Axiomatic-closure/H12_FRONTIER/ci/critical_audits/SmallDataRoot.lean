import SingularClosure.SmallDataRoot

set_option autoImplicit false
set_option Elab.async false
open Set MeasureTheory Filter
open scoped BigOperators ContDiff Topology ENNReal Interval
namespace SingularClosure
noncomputable section

example (ν : ℝ) (hν : 0 < ν) (a : CriticalSobolev 1) (ha : CriticalSigmaZero a)
    (hsmall : criticalNonlinearConstant * ‖a‖ < ν) :
    CriticalGlobalRegularity ν a :=
  @SingularClosure.SMALL_DATA_CRITICAL_REGULARITY ν hν a ha hsmall

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.SMALL_DATA_CRITICAL_REGULARITY"
#check @SingularClosure.SMALL_DATA_CRITICAL_REGULARITY
#print axioms SingularClosure.SMALL_DATA_CRITICAL_REGULARITY

example (ν : ℝ) (hν : 0 < ν) (a : CriticalSobolev 1) (ha : CriticalSigmaZero a)
    (hsmall : criticalNonlinearConstant * ‖a‖ < ν) :
    CriticalDatumAX6 ν a ∧ CriticalGlobalRegularity ν a :=
  @SingularClosure.NSE_H12_SIGMA_ZERO_SMALL_REGULARITY ν hν a ha hsmall

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.NSE_H12_SIGMA_ZERO_SMALL_REGULARITY"
#check @SingularClosure.NSE_H12_SIGMA_ZERO_SMALL_REGULARITY
#print axioms SingularClosure.NSE_H12_SIGMA_ZERO_SMALL_REGULARITY

example :
    ∃ c : ℝ, 0 < c ∧ ∀ ν : ℝ, 0 < ν → ∀ a : CriticalSobolev 1,
      CriticalSigmaZero a → ‖a‖ < c * ν →
        CriticalDatumAX6 ν a ∧ CriticalGlobalRegularity ν a :=
  @SingularClosure.NSE_H12_SIGMA_ZERO_SMALL_UNIVERSAL_CONSTANT

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.NSE_H12_SIGMA_ZERO_SMALL_UNIVERSAL_CONSTANT"
#check @SingularClosure.NSE_H12_SIGMA_ZERO_SMALL_UNIVERSAL_CONSTANT
#print axioms SingularClosure.NSE_H12_SIGMA_ZERO_SMALL_UNIVERSAL_CONSTANT

end
end SingularClosure
