import SingularClosure.CriticalInitialPhysicalFourier

set_option autoImplicit false
set_option Elab.async false
open Set MeasureTheory Filter
open scoped BigOperators ContDiff Topology ENNReal Interval
namespace SingularClosure
noncomputable section

example (a : CriticalSobolev 1) (hreal : SpectralReality (criticalCoeff 1 a))
    (hzero : SpectralMeanZero (criticalCoeff 1 a)) :
    datumFourierCoeff (criticalInitialPhysicalL2 a : Field) = criticalCoeff 1 a :=
  @SingularClosure.criticalInitialPhysicalL2_fourierCoeff a hreal hzero

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.criticalInitialPhysicalL2_fourierCoeff"
#check @SingularClosure.criticalInitialPhysicalL2_fourierCoeff
#print axioms SingularClosure.criticalInitialPhysicalL2_fourierCoeff

example (a : CriticalSobolev 1) (hreal : SpectralReality (criticalCoeff 1 a))
    (hzero : SpectralMeanZero (criticalCoeff 1 a)) :
    ‖criticalInitialPhysicalL2 a‖ = ‖criticalSobolevLower 0 1 (by norm_num) a‖ :=
  @SingularClosure.criticalInitialPhysicalL2_norm a hreal hzero

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.criticalInitialPhysicalL2_norm"
#check @SingularClosure.criticalInitialPhysicalL2_norm
#print axioms SingularClosure.criticalInitialPhysicalL2_norm

end
end SingularClosure
