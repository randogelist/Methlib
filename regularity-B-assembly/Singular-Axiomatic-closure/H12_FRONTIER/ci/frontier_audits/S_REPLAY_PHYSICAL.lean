import SingularClosure.H12Frontier.ReplayPhysical
set_option autoImplicit false
set_option Elab.async false
open Set MeasureTheory Filter
open scoped BigOperators Topology Interval NNReal ENNReal
namespace SingularClosure.H12Frontier.Replay
noncomputable section

example : ∀ (cert : NonlinearCertificate)
    (ν : ℝ) (hν : 0 ≤ ν) (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hsmall : cert.constant * ‖a‖ < ν)
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (g : ∀ n, GalerkinSolution ν
      (finiteSynthesis (φ n + 1) (criticalCoeff 1 a)) (φ n + 1))
    (u : ℝ → CriticalSobolev 1) (L : CriticalPositiveSobolevFlow ν)
    (hL : ∀ t : ℝ, 0 < t → (L.state 0 t).val = criticalCoeff 1 (u t))
    (T : ℝ) (hT : 0 ≤ T)
    (hu : ContinuousOn (fun t => criticalToTorusH0 1 (by norm_num) (u t)) (Icc (0 : ℝ) T))
    (hconv : TendstoUniformlyOn (fun n t => (g n).sobolevState 0 t)
      (fun t => criticalToTorusH0 1 (by norm_num) (u t)) atTop (Icc (0 : ℝ) T)),
    ∃ V : ℝ → CriticalSobolev (-1),
      MemLp V 2 (volume.restrict (Icc (0 : ℝ) T)) ∧
      (∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T),
        criticalCoeff (-1) (V t) = datumFourierCoeff (timeDerivative L.velocity t)) ∧
      (∫ t in Icc (0 : ℝ) T, ‖V t‖ ^ 2) ≤ (derivativeConstant cert) ν a :=
  @SingularClosure.H12Frontier.Replay.physicalNegativeHalf

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.H12Frontier.Replay.physicalNegativeHalf"
#print axioms SingularClosure.H12Frontier.Replay.physicalNegativeHalf

example : ∀ (cert : NonlinearCertificate)
    (ν : ℝ) (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hsmall : cert.constant * ‖a‖ < ν)
    (φ : ℕ → ℕ)
    (g : ∀ n, GalerkinSolution ν
      (finiteSynthesis (φ n + 1) (criticalCoeff 1 a)) (φ n + 1))
    (u : ℝ → CriticalSobolev 1) (L : CriticalPositiveSobolevFlow ν)
    (hL : ∀ t : ℝ, 0 < t → (L.state 0 t).val = criticalCoeff 1 (u t))
    (T : ℝ) (hT : 0 ≤ T)
    (hu : ContinuousOn (fun t => criticalToTorusH0 1 (by norm_num) (u t)) (Icc (0 : ℝ) T))
    (hconv : TendstoUniformlyOn (fun n t => (g n).sobolevState 0 t)
      (fun t => criticalToTorusH0 1 (by norm_num) (u t)) atTop (Icc (0 : ℝ) T)),
    IntegrableOn (fun t => physicalDissipation (L.velocity t) ^ 2) (Icc (0 : ℝ) T) volume ∧
      (∫ t in (0 : ℝ)..T, physicalDissipation (L.velocity t) ^ 2) ≤
        (‖a‖ ^ 4 - ‖u T‖ ^ 4) / (4 * (ν - cert.constant * ‖a‖)) :=
  @SingularClosure.H12Frontier.Replay.physicalQuartic

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.H12Frontier.Replay.physicalQuartic"
#print axioms SingularClosure.H12Frontier.Replay.physicalQuartic

end
end SingularClosure.H12Frontier.Replay
