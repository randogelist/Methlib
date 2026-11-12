import SingularityDisprovement.Scaling

open Set MeasureTheory SingularClosure SingularityDisprovement
open scoped ENNReal

example (ν r : ℝ) (hr : 0 < r) (a : CriticalSobolev 1) (ha : CriticalSigmaZero a) :
    CriticalSigmaZero (r • a) ∧
    ‖r • a‖ = r * ‖a‖ ∧
    ‖physicalL2 (r • a)‖ = r * ‖physicalL2 a‖ ∧
    calibratedScore ν (r • a) = r ^ 2 * calibratedScore ν a ∧
    (kineticDensity (r • a) =ᵐ[volume.restrict unitCube]
      fun x => r ^ 2 * kineticDensity a x) ∧
    (EssUnbounded a → EssUnbounded (r • a)) ∧
    (EssUnbounded a ↔ densityEssSup a = ⊤) :=
  POSITIVE_SCALING_LAWS ν r hr a ha

#eval IO.println "EXACT_TYPE_PASS:SingularityDisprovement.POSITIVE_SCALING_LAWS"
#check @SingularityDisprovement.POSITIVE_SCALING_LAWS
#print axioms SingularityDisprovement.POSITIVE_SCALING_LAWS

