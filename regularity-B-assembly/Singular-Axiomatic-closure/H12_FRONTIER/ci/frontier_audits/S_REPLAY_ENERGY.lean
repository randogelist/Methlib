import SingularClosure.H12Frontier.ReplayEnergy
set_option autoImplicit false
set_option Elab.async false
open Set MeasureTheory Filter
open scoped BigOperators Topology Interval NNReal ENNReal
namespace SingularClosure.H12Frontier.Replay
noncomputable section

example : ∀ (cert : NonlinearCertificate)
    {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N)
    {t : ℝ} (ht : 0 ≤ t),
    criticalEnergyRate ν 1 N (g.coeff t) +
      2 * (ν - cert.constant * Real.sqrt (criticalEnergy 1 N (g.coeff t))) *
        criticalEnergy 3 N (g.coeff t) ≤ 0 :=
  @SingularClosure.H12Frontier.Replay.differentialInequality

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.H12Frontier.Replay.differentialInequality"
#print axioms SingularClosure.H12Frontier.Replay.differentialInequality

example : ∀ (cert : NonlinearCertificate)
    {ν T : ℝ} {N : ℕ} (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hsmall : cert.constant * ‖a‖ < ν) (hT : 0 ≤ T)
    (g : GalerkinSolution ν (finiteSynthesis N (criticalCoeff 1 a)) N),
    ∀ t ∈ Icc 0 T, criticalEnergy 1 N (g.coeff t) ≤ ‖a‖ ^ 2 :=
  @SingularClosure.H12Frontier.Replay.energyInvariant

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.H12Frontier.Replay.energyInvariant"
#print axioms SingularClosure.H12Frontier.Replay.energyInvariant

example : ∀ (cert : NonlinearCertificate)
    {ν T : ℝ} {N : ℕ} (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hsmall : cert.constant * ‖a‖ < ν) (hT : 0 ≤ T)
    (g : GalerkinSolution ν (finiteSynthesis N (criticalCoeff 1 a)) N),
    ∀ t ∈ Icc 0 T,
      criticalEnergy 1 N (g.coeff t) + 2 * (ν - cert.constant * ‖a‖) *
        (∫ s in (0 : ℝ)..t, criticalEnergy 3 N (g.coeff s)) ≤ ‖a‖ ^ 2 :=
  @SingularClosure.H12Frontier.Replay.dissipationBudget

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.H12Frontier.Replay.dissipationBudget"
#print axioms SingularClosure.H12Frontier.Replay.dissipationBudget

example : ∀ (cert : NonlinearCertificate)
    {ν T : ℝ} {N : ℕ} (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hsmall : cert.constant * ‖a‖ < ν) (hT : 0 ≤ T)
    (g : GalerkinSolution ν (finiteSynthesis N (criticalCoeff 1 a)) N),
    (∫ t in (0 : ℝ)..T, coefficientDissipation N (g.coeff t) ^ 2) ≤
      (‖a‖ ^ 4 - criticalEnergy 1 N (g.coeff T) ^ 2) /
        (4 * (ν - cert.constant * ‖a‖)) :=
  @SingularClosure.H12Frontier.Replay.sharpSquareBudget

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.H12Frontier.Replay.sharpSquareBudget"
#print axioms SingularClosure.H12Frontier.Replay.sharpSquareBudget

example : ∀ (cert : NonlinearCertificate)
    {ν T : ℝ} {N : ℕ} (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hsmall : cert.constant * ‖a‖ < ν) (hT : 0 ≤ T)
    (g : GalerkinSolution ν (finiteSynthesis N (criticalCoeff 1 a)) N),
    budget6 N g.coeff T ≤
      ENNReal.ofReal (‖a‖ ^ 4 / (4 * (ν - cert.constant * ‖a‖))) :=
  @SingularClosure.H12Frontier.Replay.sixChannelBudget

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.H12Frontier.Replay.sixChannelBudget"
#print axioms SingularClosure.H12Frontier.Replay.sixChannelBudget

example : ∀ (cert : NonlinearCertificate)
    (ν : ℝ) (_hν : 0 < ν) (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (_hsol : SpectralSolenoidal (criticalCoeff 1 a))
    (_hzero : SpectralMeanZero (criticalCoeff 1 a))
    (hsmall : cert.constant * ‖a‖ < ν),
    CriticalDatumAX6 ν a :=
  @SingularClosure.H12Frontier.Replay.datumAX6

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.H12Frontier.Replay.datumAX6"
#print axioms SingularClosure.H12Frontier.Replay.datumAX6

end
end SingularClosure.H12Frontier.Replay
