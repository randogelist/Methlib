import SingularityDisprovement.DyadicPhysical

open MeasureTheory SingularClosure SingularityDisprovement

example (ν : ℝ) :
    (physicalL2 (dyadicSeed ν) : Field) =ᵐ[volume.restrict unitCube]
      dyadicPhysicalRepresentative ν :=
  DYADIC_PHYSICAL_IDENTIFICATION ν

#eval IO.println "EXACT_TYPE_PASS:SingularityDisprovement.DYADIC_PHYSICAL_IDENTIFICATION"
#check @SingularityDisprovement.DYADIC_PHYSICAL_IDENTIFICATION
#print axioms SingularityDisprovement.DYADIC_PHYSICAL_IDENTIFICATION
