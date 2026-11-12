import SingularClosure.H12Frontier.ReplayCompactness
set_option autoImplicit false
set_option Elab.async false
open Set MeasureTheory Filter
open scoped BigOperators Topology Interval NNReal ENNReal
namespace SingularClosure.H12Frontier.Replay
noncomputable section

example : ∀ (cert : NonlinearCertificate)
    {ν : ℝ} {N : ℕ} (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hsmall : cert.constant * ‖a‖ < ν)
    (g : GalerkinSolution ν (finiteSynthesis N (criticalCoeff 1 a)) N)
    {t : ℝ} (ht : 0 ≤ t),
    ‖g.criticalState 1 t‖ ≤ ‖a‖ :=
  @SingularClosure.H12Frontier.Replay.stateNormBound

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.H12Frontier.Replay.stateNormBound"
#print axioms SingularClosure.H12Frontier.Replay.stateNormBound

example : ∀ (cert : NonlinearCertificate)
    {ν : ℝ} (a : CriticalSobolev 1)
    (hsmall : cert.constant * ‖a‖ < ν),
    0 ≤ (dissipationConstant cert) ν a :=
  @SingularClosure.H12Frontier.Replay.dissipationConstant_nonneg

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.H12Frontier.Replay.dissipationConstant_nonneg"
#print axioms SingularClosure.H12Frontier.Replay.dissipationConstant_nonneg

example : ∀ (cert : NonlinearCertificate)
    {ν : ℝ} (a : CriticalSobolev 1)
    (hsmall : cert.constant * ‖a‖ < ν),
    0 ≤ (derivativeConstant cert) ν a :=
  @SingularClosure.H12Frontier.Replay.derivativeConstant_nonneg

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.H12Frontier.Replay.derivativeConstant_nonneg"
#print axioms SingularClosure.H12Frontier.Replay.derivativeConstant_nonneg

example : ∀ (cert : NonlinearCertificate)
    {ν T : ℝ} {N : ℕ} (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hsmall : cert.constant * ‖a‖ < ν) (hT : 0 ≤ T)
    (g : GalerkinSolution ν (finiteSynthesis N (criticalCoeff 1 a)) N),
    (∫ t in (0 : ℝ)..T, ‖g.criticalState 3 t‖ ^ 2) ≤ (dissipationConstant cert) ν a :=
  @SingularClosure.H12Frontier.Replay.stateThreeIntegral

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.H12Frontier.Replay.stateThreeIntegral"
#print axioms SingularClosure.H12Frontier.Replay.stateThreeIntegral

example : ∀ (cert : NonlinearCertificate)
    (ν : ℝ) (hν : 0 ≤ ν) (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hsol : SpectralSolenoidal (criticalCoeff 1 a))
    (hsmall : cert.constant * ‖a‖ < ν),
    ∃ u : ℝ → CriticalSobolev 1, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      (∀ t, 0 ≤ t → ‖u t‖ ≤ ‖a‖) ∧
      ContinuousOn (fun t => criticalToTorusH0 1 (by norm_num) (u t)) (Ici 0) ∧
      (∀ T : ℝ, TendstoUniformlyOn
        (fun n t => (criticalDatumGalerkinFamily ν hν a hreal hsol (φ n)).sobolevState 0 t)
        (fun t => criticalToTorusH0 1 (by norm_num) (u t)) atTop (Icc (0 : ℝ) T)) ∧
      ∀ T : ℝ, 0 ≤ T → ∃ u1 : TimeH1L2 T,
        Tendsto
          (fun n => (criticalDatumGalerkinFamily ν hν a hreal hsol (φ n)).criticalTimeH1L2 T)
          atTop (𝓝 u1) :=
  @SingularClosure.H12Frontier.Replay.globalCompactness

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.H12Frontier.Replay.globalCompactness"
#print axioms SingularClosure.H12Frontier.Replay.globalCompactness

end
end SingularClosure.H12Frontier.Replay
