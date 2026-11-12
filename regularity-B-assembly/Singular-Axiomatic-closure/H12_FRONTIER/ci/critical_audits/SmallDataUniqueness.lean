import SingularClosure.SmallDataUniqueness

set_option autoImplicit false
set_option Elab.async false
open Set MeasureTheory Filter
open scoped BigOperators ContDiff Topology ENNReal Interval
namespace SingularClosure
noncomputable section

example (ν : ℝ) (hν : 0 < ν) (a : CriticalSobolev 1) (ha : CriticalSigmaZero a)
    (hsmall : criticalNonlinearConstant * ‖a‖ < ν) :
    CriticalDatumAX6 ν a ∧ ∃ U : CriticalRegularSolution ν a,
      U.lerayHopfUnique ∧
      (∀ T : ℝ, 0 < T →
        MemLp (fun t => criticalSpatialNorm 6 (U.flow.velocity t)) 4
          (volume.restrict (Ioc (0 : ℝ) T))) :=
  @SingularClosure.SMALL_DATA_CRITICAL_LERAY_HOPF_COMPARISON ν hν a ha hsmall

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.SMALL_DATA_CRITICAL_LERAY_HOPF_COMPARISON"
#check @SingularClosure.SMALL_DATA_CRITICAL_LERAY_HOPF_COMPARISON
#print axioms SingularClosure.SMALL_DATA_CRITICAL_LERAY_HOPF_COMPARISON

end
end SingularClosure
