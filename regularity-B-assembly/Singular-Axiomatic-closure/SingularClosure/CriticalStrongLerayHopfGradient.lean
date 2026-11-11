import SingularClosure.CriticalStrongLerayHopfEnergy
import SingularClosure.CriticalGradientL2Measurable

/-! The actual physical gradient is in Bochner L2 in time and space. -/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory

namespace SingularClosure
noncomputable section

theorem CriticalRegularSolution.leray_gradient_energy_class
    {ν : ℝ} {a : CriticalSobolev 1} (U : CriticalRegularSolution ν a)
    (T : ℝ) (hT : 0 ≤ T)
    (hQ : IntegrableOn (fun t => physicalDissipation (U.flow.velocity t) ^ 2)
      (Icc (0 : ℝ) T) volume) :
    MemLp (fun t => criticalL2Representative (U.lerayGradient t)) 2
      (volume.restrict (Ioc (0 : ℝ) T)) :=
  U.leray_gradient_energy_class_of_measurable T hT hQ
    (criticalPositive_gradientL2_aestronglyMeasurable U.flow T)

end
end SingularClosure
