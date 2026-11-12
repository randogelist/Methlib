import QuasiFeffermanB.FourierEnergy
import QuasiFeffermanB.Semantics
import SingularClosure.CriticalSerrinUniqueness

/-! Concrete analytic interface for the exact small-Hhalf restart admission.
This is a proposition to be proved, not an axiom or a field of the input datum.
-/
set_option autoImplicit false
set_option Elab.async true

open Set Filter MeasureTheory
open scoped ContDiff ENNReal Topology Interval

namespace QuasiFeffermanB
open SingularClosure
noncomputable section

structure RegularReference (ν : ℝ) (a : CriticalPhysicalL2) where
  flow : CriticalPositiveSobolevFlow ν
  trace : Tendsto
    (fun t => eLpNorm (flow.velocity t - (a : Field)) 2 (volume.restrict unitCube))
    (𝓝[>] (0 : ℝ)) (𝓝 0)
  serrin : ∀ T : ℝ, 0 < T →
    MemLp (fun t => criticalSpatialNorm 6 (flow.velocity t)) 4
      (volume.restrict (Ioc (0 : ℝ) T))

def ExactH1Admission (ν : ℝ) : Prop :=
  ∀ (b : Field) (D : Vec → (Vec →L[ℝ] Vec)),
    CriticalPhysicalH1 b D → EnergySigmaZero (criticalL2Representative b) →
    physicalHalfEnergy b < ENNReal.ofReal (2 * Real.pi * ν ^ 2) →
    Nonempty (RegularReference ν (criticalL2Representative b))

end
end QuasiFeffermanB
