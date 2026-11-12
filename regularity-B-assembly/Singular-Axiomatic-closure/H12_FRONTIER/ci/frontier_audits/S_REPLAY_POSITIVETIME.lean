import SingularClosure.H12Frontier.ReplayPositiveTime
set_option autoImplicit false
set_option Elab.async false
open Set MeasureTheory Filter
open scoped BigOperators Topology Interval NNReal ENNReal
namespace SingularClosure.H12Frontier.Replay
noncomputable section

example : ∀ (cert : NonlinearCertificate)
    (ν : ℝ) (hν : 0 < ν) (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hsmall : cert.constant * ‖a‖ < ν)
    (τ : ℝ) (hτ : 0 < τ) (T : ℝ) (hτT : τ ≤ T),
    ∃ L : ℝ, 0 ≤ L ∧ ∀ N : ℕ,
      ∀ g : GalerkinSolution ν (finiteSynthesis N (criticalCoeff 1 a)) N,
      ∀ t ∈ Icc τ T,
        coefficientDissipation N (g.coeff t) +
          ν * (∫ s in τ..t, coefficientLaplacianSquare N (g.coeff s)) ≤ L :=
  @SingularClosure.H12Frontier.Replay.positiveEnstrophy

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.H12Frontier.Replay.positiveEnstrophy"
#print axioms SingularClosure.H12Frontier.Replay.positiveEnstrophy

example : ∀ (cert : NonlinearCertificate)
    (ν : ℝ) (hν : 0 < ν) (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hsmall : cert.constant * ‖a‖ < ν)
    (τ : ℝ) (hτ : 0 < τ) (T : ℝ) (hτT : τ ≤ T),
    ∃ S : ℝ, 0 ≤ S ∧ ∀ N : ℕ,
      ∀ g : GalerkinSolution ν (finiteSynthesis N (criticalCoeff 1 a)) N,
        (∫ t in τ..T, highOrderEnergy 2 N (g.coeff t)) ≤ S :=
  @SingularClosure.H12Frontier.Replay.positiveH2

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.H12Frontier.Replay.positiveH2"
#print axioms SingularClosure.H12Frontier.Replay.positiveH2

example : ∀ (cert : NonlinearCertificate)
    (ν : ℝ) (hν : 0 < ν) (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hsmall : cert.constant * ‖a‖ < ν)
    (m : ℕ) (τ T : ℝ) (hτ : 0 < τ) (hτT : τ < T),
    ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ,
      ∀ g : GalerkinSolution ν (finiteSynthesis N (criticalCoeff 1 a)) N,
      ∀ t ∈ Icc τ T, highOrderEnergy m N (g.coeff t) +
        ν * (∫ s in τ..t, highOrderEnergy (m + 1) N (g.coeff s)) ≤ B :=
  @SingularClosure.H12Frontier.Replay.positiveAllOrders

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.H12Frontier.Replay.positiveAllOrders"
#print axioms SingularClosure.H12Frontier.Replay.positiveAllOrders

example : ∀ (cert : NonlinearCertificate)
    (ν : ℝ) (hν : 0 < ν) (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hsmall : cert.constant * ‖a‖ < ν)
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (g : ∀ n : ℕ, GalerkinSolution ν
      (finiteSynthesis (φ n + 1) (criticalCoeff 1 a)) (φ n + 1))
    (u : ℝ → TorusSobolev 0) (hu : ContinuousOn u (Ici 0))
    (hconv : ∀ T : ℝ, 0 < T → TendstoUniformlyOn
      (fun n t => (g n).sobolevState 0 t) u atTop (Icc (0 : ℝ) T)),
    ∃ L : CriticalPositiveSobolevFlow ν, ∀ t : ℝ, 0 < t → L.state 0 t = u t :=
  @SingularClosure.H12Frontier.Replay.positiveFlow

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.H12Frontier.Replay.positiveFlow"
#print axioms SingularClosure.H12Frontier.Replay.positiveFlow

end
end SingularClosure.H12Frontier.Replay
