import SingularClosure.H12Frontier.ReplayDerivative
set_option autoImplicit false
set_option Elab.async false
open Set MeasureTheory Filter
open scoped BigOperators Topology Interval NNReal ENNReal
namespace SingularClosure.H12Frontier.Replay
noncomputable section

example : ∀ (cert : NonlinearCertificate)
    {ν T : ℝ} {N : ℕ} (hν : 0 ≤ ν) (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hsmall : cert.constant * ‖a‖ < ν) (hT : 0 ≤ T)
    (g : GalerkinSolution ν (finiteSynthesis N (criticalCoeff 1 a)) N)
    {t : ℝ} (ht : t ∈ Icc 0 T),
    ‖g.criticalRhs (-1) t‖ ≤
      (ν + criticalTransportConstant * ‖a‖) * Real.sqrt (criticalEnergy 3 N (g.coeff t)) :=
  @SingularClosure.H12Frontier.Replay.timeDerivativePointwise

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.H12Frontier.Replay.timeDerivativePointwise"
#print axioms SingularClosure.H12Frontier.Replay.timeDerivativePointwise

example : ∀ (cert : NonlinearCertificate)
    {ν T : ℝ} {N : ℕ} (hν : 0 ≤ ν) (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hsmall : cert.constant * ‖a‖ < ν) (hT : 0 ≤ T)
    (g : GalerkinSolution ν (finiteSynthesis N (criticalCoeff 1 a)) N)
    {t : ℝ} (ht : t ∈ Icc 0 T),
    ‖g.criticalRhs (-1) t‖ ^ 2 ≤
      (ν + criticalTransportConstant * ‖a‖) ^ 2 * criticalEnergy 3 N (g.coeff t) :=
  @SingularClosure.H12Frontier.Replay.timeDerivativeSquare

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.H12Frontier.Replay.timeDerivativeSquare"
#print axioms SingularClosure.H12Frontier.Replay.timeDerivativeSquare

example : ∀ (cert : NonlinearCertificate)
    {ν T : ℝ} {N : ℕ} (hν : 0 ≤ ν) (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hsmall : cert.constant * ‖a‖ < ν) (hT : 0 ≤ T)
    (g : GalerkinSolution ν (finiteSynthesis N (criticalCoeff 1 a)) N),
    (∫ t in (0 : ℝ)..T, ‖g.criticalRhs (-1) t‖ ^ 2) ≤
      (ν + criticalTransportConstant * ‖a‖) ^ 2 * ‖a‖ ^ 2 /
        (2 * (ν - cert.constant * ‖a‖)) :=
  @SingularClosure.H12Frontier.Replay.timeDerivativeBudget

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.H12Frontier.Replay.timeDerivativeBudget"
#print axioms SingularClosure.H12Frontier.Replay.timeDerivativeBudget

end
end SingularClosure.H12Frontier.Replay
