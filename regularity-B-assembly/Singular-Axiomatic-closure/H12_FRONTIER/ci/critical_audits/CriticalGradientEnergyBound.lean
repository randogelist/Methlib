import SingularClosure.CriticalGradientEnergyBound

set_option autoImplicit false
set_option Elab.async false
open Set MeasureTheory Filter
open scoped BigOperators ContDiff Topology ENNReal Interval
namespace SingularClosure
noncomputable section

example :
    ∃ C : ℝ, 0 < C ∧ ∀ (ν : ℝ), 0 < ν →
      ∀ (u v : Field) (G : Vec → (Vec →L[ℝ] Vec)),
      MemLp u 6 (volume.restrict unitCube) → CriticalPhysicalH1 v G →
      abs (criticalRoughTransport v G u) ≤
        (ν / 2) * criticalGradientEnergy G +
          (216 * C ^ 4 * (criticalSpatialNorm 6 u) ^ 4 / ν ^ 3 +
            3 * C ^ 2 * (criticalSpatialNorm 6 u) ^ 2 / ν) * physicalEnergy v :=
  @SingularClosure.CRITICAL_ROUGH_TRANSPORT_ENERGY_BOUND

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.CRITICAL_ROUGH_TRANSPORT_ENERGY_BOUND"
#check @SingularClosure.CRITICAL_ROUGH_TRANSPORT_ENERGY_BOUND
#print axioms SingularClosure.CRITICAL_ROUGH_TRANSPORT_ENERGY_BOUND

end
end SingularClosure
