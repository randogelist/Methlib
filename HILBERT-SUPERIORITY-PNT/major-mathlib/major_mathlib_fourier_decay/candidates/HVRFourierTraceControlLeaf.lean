import Mathlib.Analysis.Fourier.RiemannLebesgueLemma

/-! Positive control only. This intentionally invokes the target. -/
noncomputable section
open Filter MeasureTheory
open scoped Topology

namespace HVRFourierTraceControlLeaf

theorem direct_target (g : ℝ → ℂ) :
    Tendsto (fun ξ : ℝ => ∫ t : ℝ, Real.fourierChar (-(t * ξ)) • g t)
      (cocompact ℝ) (𝓝 0) :=
  Real.tendsto_integral_exp_smul_cocompact g

end HVRFourierTraceControlLeaf
