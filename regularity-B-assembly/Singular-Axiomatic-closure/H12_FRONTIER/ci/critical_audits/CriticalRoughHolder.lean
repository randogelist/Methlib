import SingularClosure.CriticalRoughHolder

set_option autoImplicit false
set_option Elab.async false
open Set MeasureTheory Filter
open scoped BigOperators ContDiff Topology ENNReal Interval
namespace SingularClosure
noncomputable section

example (u v : Field) (G : Vec → (Vec →L[ℝ] Vec))
    (hu : MemLp u 6 (volume.restrict unitCube))
    (hv : MemLp v 3 (volume.restrict unitCube))
    (hG : MemLp G 2 (volume.restrict unitCube)) :
    IntegrableOn (fun x => inner ℝ (u x) (G x (v x))) unitCube volume ∧
    ENNReal.ofReal (abs (criticalRoughTransport v G u)) ≤
      (eLpNorm u 6 (volume.restrict unitCube) *
        eLpNorm v 3 (volume.restrict unitCube)) *
          eLpNorm G 2 (volume.restrict unitCube) :=
  @SingularClosure.CRITICAL_ROUGH_TRANSPORT_HOLDER u v G hu hv hG

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.CRITICAL_ROUGH_TRANSPORT_HOLDER"
#check @SingularClosure.CRITICAL_ROUGH_TRANSPORT_HOLDER
#print axioms SingularClosure.CRITICAL_ROUGH_TRANSPORT_HOLDER

end
end SingularClosure
