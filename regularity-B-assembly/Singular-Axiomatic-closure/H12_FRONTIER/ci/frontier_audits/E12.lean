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
    ∀ (ν : ℝ) (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hsmall : frontierConstant * ‖a‖ < ν)
    (φ : ℕ → ℕ)
    (g : ∀ n, GalerkinSolution ν
      (finiteSynthesis (φ n + 1) (criticalCoeff 1 a)) (φ n + 1))
    (u : ℝ → CriticalSobolev 1) (T : ℝ) (hT : 0 ≤ T)
    (hconv : TendstoUniformlyOn (fun n t => (g n).sobolevState 0 t)
      (fun t => criticalToTorusH0 1 (by norm_num) (u t)) atTop (Icc (0 : ℝ) T)),
    ENNReal.ofReal (‖u T‖ ^ 4) +
      ENNReal.ofReal (4 * (ν - frontierConstant * ‖a‖)) *
        (∫⁻ t in Icc (0 : ℝ) T,
          criticalExtendedSquare 2 (criticalCoeff 1 (u t)) ^ 2) ≤ ENNReal.ofReal (‖a‖ ^ 4) :=
  @SingularClosure.H12Frontier.frontierLimitSharpQuartic

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.H12Frontier.frontierLimitSharpQuartic"
#print axioms SingularClosure.H12Frontier.frontierLimitSharpQuartic

end
end SingularClosure.H12Frontier
