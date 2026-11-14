import SingularClosure.H12Frontier.ReplayLimit
set_option autoImplicit false
set_option Elab.async false
open Set MeasureTheory Filter
open scoped BigOperators Topology Interval NNReal ENNReal
namespace SingularClosure.H12Frontier.Replay
noncomputable section

example : ∀ (cert : NonlinearCertificate)
    (ν : ℝ) (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hsmall : cert.constant * ‖a‖ < ν)
    (φ : ℕ → ℕ)
    (g : ∀ n, GalerkinSolution ν
      (finiteSynthesis (φ n + 1) (criticalCoeff 1 a)) (φ n + 1))
    (u : ℝ → CriticalSobolev 1) (T : ℝ) (hT : 0 ≤ T)
    (hconv : TendstoUniformlyOn (fun n t => (g n).sobolevState 0 t)
      (fun t => criticalToTorusH0 1 (by norm_num) (u t)) atTop (Icc (0 : ℝ) T)),
    ENNReal.ofReal (‖u T‖ ^ 4) +
      ENNReal.ofReal (4 * (ν - cert.constant * ‖a‖)) *
        (∫⁻ t in Icc (0 : ℝ) T,
          criticalExtendedSquare 2 (criticalCoeff 1 (u t)) ^ 2) ≤ ENNReal.ofReal (‖a‖ ^ 4) :=
  @SingularClosure.H12Frontier.Replay.limitQuartic

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.H12Frontier.Replay.limitQuartic"
#print axioms SingularClosure.H12Frontier.Replay.limitQuartic

example : ∀ (cert : NonlinearCertificate)
    (ν : ℝ) (hν : 0 ≤ ν) (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hsmall : cert.constant * ‖a‖ < ν)
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
      (∫ t in Icc (0 : ℝ) T, ‖V t‖ ^ 2) ≤ (derivativeConstant cert) ν a :=
  @SingularClosure.H12Frontier.Replay.limitNegativeHalf

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.H12Frontier.Replay.limitNegativeHalf"
#print axioms SingularClosure.H12Frontier.Replay.limitNegativeHalf

end
end SingularClosure.H12Frontier.Replay
