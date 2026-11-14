import SingularClosure.CriticalSerrinEstimate

set_option autoImplicit false
set_option Elab.async false
open Set MeasureTheory Filter
open scoped BigOperators ContDiff Topology ENNReal Interval
namespace SingularClosure
noncomputable section

example :
    ∃ A : ℝ, 0 < A ∧ ∀ (u v : Field) (G : Vec → (Vec →L[ℝ] Vec)),
      MemLp u 6 (volume.restrict unitCube) → CriticalPhysicalH1 v G →
      abs (criticalRoughTransport v G u) ≤
        A * criticalSpatialNorm 6 u * Real.sqrt (criticalSpatialNorm 2 v) *
          Real.sqrt (criticalSpatialNorm 2 G + criticalSpatialNorm 2 v) *
            criticalSpatialNorm 2 G :=
  @SingularClosure.CRITICAL_ROUGH_TRANSPORT_INTERPOLATED

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.CRITICAL_ROUGH_TRANSPORT_INTERPOLATED"
#check @SingularClosure.CRITICAL_ROUGH_TRANSPORT_INTERPOLATED
#print axioms SingularClosure.CRITICAL_ROUGH_TRANSPORT_INTERPOLATED

end
end SingularClosure
