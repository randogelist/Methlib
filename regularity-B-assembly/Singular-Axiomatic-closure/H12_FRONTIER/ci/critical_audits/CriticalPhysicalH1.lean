import SingularClosure.CriticalPhysicalH1

set_option autoImplicit false
set_option Elab.async false
open Set MeasureTheory Filter
open scoped BigOperators ContDiff Topology ENNReal Interval
namespace SingularClosure
noncomputable section

example :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (v : Field) (G : Vec → (Vec →L[ℝ] Vec)),
      CriticalPhysicalH1 v G →
      eLpNorm v 6 (volume.restrict unitCube) ≤
        (SNormLESNormFDerivOfEqConst Vec (volume : Measure Vec) 2 : ℝ≥0∞) *
          (343 : ℝ≥0∞) ^ (1 / 2 : ℝ) *
          (eLpNorm G 2 (volume.restrict unitCube) +
            ENNReal.ofReal K * eLpNorm v 2 (volume.restrict unitCube)) :=
  @SingularClosure.CRITICAL_PHYSICAL_H1_L6

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.CRITICAL_PHYSICAL_H1_L6"
#check @SingularClosure.CRITICAL_PHYSICAL_H1_L6
#print axioms SingularClosure.CRITICAL_PHYSICAL_H1_L6

end
end SingularClosure
