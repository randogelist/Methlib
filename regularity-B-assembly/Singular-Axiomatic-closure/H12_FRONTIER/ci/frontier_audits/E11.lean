import SingularClosure.H12Frontier.LimitMilestones

/-! Concrete specialization; every nonlinear certificate is constructed from
proved physical inequalities. All registered datum hypotheses are retained. -/
set_option autoImplicit false
set_option Elab.async false
open Set MeasureTheory Filter
open scoped BigOperators Topology Interval NNReal ENNReal
namespace SingularClosure.H12Frontier
noncomputable section

example :
    ∀ (ν : ℝ) (hν : 0 ≤ ν) (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hsmall : frontierConstant * ‖a‖ < ν)
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (g : ∀ n, GalerkinSolution ν
      (finiteSynthesis (φ n + 1) (criticalCoeff 1 a)) (φ n + 1))
    (u : ℝ → CriticalSobolev 1) (T : ℝ) (hT : 0 ≤ T)
    (hu : ContinuousOn (fun t => criticalToTorusH0 1 (by norm_num) (u t)) (Icc (0 : ℝ) T))
    (hconv : TendstoUniformlyOn (fun n t => (g n).sobolevState 0 t)
      (fun t => criticalToTorusH0 1 (by norm_num) (u t)) atTop (Icc (0 : ℝ) T)),
    ∃ V : ℝ → CriticalSobolev (-1),
      MemLp V 2 (volume.restrict (Icc (0 : ℝ) T)) ∧
      (∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T),
        criticalCoeff (-1) (V t) = fullFourierRhs ν (criticalToTorusH0 1 (by norm_num) (u t))) ∧
      (∫ t in Icc (0 : ℝ) T, ‖V t‖ ^ 2) ≤ frontierDerivativeConstant ν a :=
  @SingularClosure.H12Frontier.frontierLimitNegativeHalf

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.H12Frontier.frontierLimitNegativeHalf"
#print axioms SingularClosure.H12Frontier.frontierLimitNegativeHalf

end
end SingularClosure.H12Frontier
