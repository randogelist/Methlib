import SingularClosure.H12Frontier.NonlinearBound
import SingularClosure.H12Frontier.ReplayDerivative

/-! Concrete specialization; every nonlinear certificate is constructed from
proved physical inequalities. All registered datum hypotheses are retained. -/
set_option autoImplicit false
set_option Elab.async true
open Set MeasureTheory Filter
open scoped BigOperators Topology Interval NNReal ENNReal
namespace SingularClosure.H12Frontier
noncomputable section

theorem frontierTimeDerivativeBudget :
    ∀ {ν T : ℝ} {N : ℕ} (hν : 0 ≤ ν) (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hsmall : frontierConstant * ‖a‖ < ν) (hT : 0 ≤ T)
    (g : GalerkinSolution ν (finiteSynthesis N (criticalCoeff 1 a)) N),
    (∫ t in (0 : ℝ)..T, ‖g.criticalRhs (-1) t‖ ^ 2) ≤
      (ν + criticalTransportConstant * ‖a‖) ^ 2 * ‖a‖ ^ 2 /
        (2 * (ν - frontierConstant * ‖a‖)) :=
  @Replay.timeDerivativeBudget frontierCertificate

end
end SingularClosure.H12Frontier
