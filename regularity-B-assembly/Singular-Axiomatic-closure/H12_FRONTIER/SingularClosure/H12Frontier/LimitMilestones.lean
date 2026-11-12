import SingularClosure.H12Frontier.NonlinearBound
import SingularClosure.H12Frontier.ReplayLimit

/-! Concrete specialization; every nonlinear certificate is constructed from
proved physical inequalities. All registered datum hypotheses are retained. -/
set_option autoImplicit false
set_option Elab.async true
open Set MeasureTheory Filter
open scoped BigOperators Topology Interval NNReal ENNReal
namespace SingularClosure.H12Frontier
noncomputable section

def frontierDissipationConstant (ν : ℝ) (a : CriticalSobolev 1) : ℝ :=
  Replay.dissipationConstant frontierCertificate ν a

def frontierDerivativeConstant (ν : ℝ) (a : CriticalSobolev 1) : ℝ :=
  Replay.derivativeConstant frontierCertificate ν a

theorem frontierLimitNegativeHalf :
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
  @Replay.limitNegativeHalf frontierCertificate

theorem frontierLimitSharpQuartic :
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
  @Replay.limitQuartic frontierCertificate

end
end SingularClosure.H12Frontier
