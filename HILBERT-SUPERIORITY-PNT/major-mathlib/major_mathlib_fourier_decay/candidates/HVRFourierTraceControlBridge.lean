import HVRFourierTraceControlLeaf

/-! Tests traversal through a separately compiled project theorem. -/
noncomputable section
open Filter MeasureTheory
open scoped Topology

namespace HVRFourierTraceControlBridge

theorem indirect_target (g : ℝ → ℂ) :
    Tendsto (fun ξ : ℝ => ∫ t : ℝ, Real.fourierChar (-(t * ξ)) • g t)
      (cocompact ℝ) (𝓝 0) :=
  HVRFourierTraceControlLeaf.direct_target g

end HVRFourierTraceControlBridge
