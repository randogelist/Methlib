import SingularClosure.H12Frontier.NonlinearBound
import SingularClosure.H12Frontier.ReplayEnergy

/-! Concrete specialization; every nonlinear certificate is constructed from
proved physical inequalities. All registered datum hypotheses are retained. -/
set_option autoImplicit false
set_option Elab.async true
open Set MeasureTheory Filter
open scoped BigOperators Topology Interval NNReal ENNReal
namespace SingularClosure.H12Frontier
noncomputable section

theorem frontierGalerkinEnergyInvariant :
    ∀ {ν T : ℝ} {N : ℕ} (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hsmall : frontierConstant * ‖a‖ < ν) (hT : 0 ≤ T)
    (g : GalerkinSolution ν (finiteSynthesis N (criticalCoeff 1 a)) N),
    ∀ t ∈ Icc 0 T, criticalEnergy 1 N (g.coeff t) ≤ ‖a‖ ^ 2 :=
  @Replay.energyInvariant frontierCertificate

theorem frontierDissipationBudget :
    ∀ {ν T : ℝ} {N : ℕ} (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hsmall : frontierConstant * ‖a‖ < ν) (hT : 0 ≤ T)
    (g : GalerkinSolution ν (finiteSynthesis N (criticalCoeff 1 a)) N),
    ∀ t ∈ Icc 0 T,
      criticalEnergy 1 N (g.coeff t) + 2 * (ν - frontierConstant * ‖a‖) *
        (∫ s in (0 : ℝ)..t, criticalEnergy 3 N (g.coeff s)) ≤ ‖a‖ ^ 2 :=
  @Replay.dissipationBudget frontierCertificate

theorem frontierSharpQuarticBudget :
    ∀ {ν T : ℝ} {N : ℕ} (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hsmall : frontierConstant * ‖a‖ < ν) (hT : 0 ≤ T)
    (g : GalerkinSolution ν (finiteSynthesis N (criticalCoeff 1 a)) N),
    ∀ t ∈ Icc 0 T,
      criticalEnergy 1 N (g.coeff t) ^ 2 +
        4 * (ν - frontierConstant * ‖a‖) *
          (∫ s in (0 : ℝ)..t, criticalEnergy 2 N (g.coeff s) ^ 2) ≤
        criticalEnergy 1 N (g.coeff 0) ^ 2 := by
  intro ν T N a hreal hsmall hT g
  exact CRITICAL_SQUARE_BUDGET hT frontierConstant_pos.le (norm_nonneg a) hsmall
    ((g.criticalEnergy_continuousOn 1).mono (fun t ht => ht.1))
    ((g.criticalEnergy_continuousOn 2).mono (fun t ht => ht.1))
    (fun t _ => criticalEnergy_nonneg 1 N (g.coeff t))
    (fun t _ => criticalEnergy_nonneg 3 N (g.coeff t))
    (criticalGalerkin_criticalEnergy_initial_le 1 a hreal g)
    (fun t ht => g.criticalEnergy_balance 1 ht.1)
    (fun t ht => Replay.differentialInequality frontierCertificate g ht.1)
    (fun t _ => criticalEnergy_interpolation N (g.coeff t))

end
end SingularClosure.H12Frontier
