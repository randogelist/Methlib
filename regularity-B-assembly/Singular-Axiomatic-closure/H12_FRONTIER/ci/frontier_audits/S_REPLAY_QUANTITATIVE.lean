import SingularClosure.H12Frontier.ReplayQuantitative
set_option autoImplicit false
set_option Elab.async false
open Set MeasureTheory Filter
open scoped BigOperators Topology Interval NNReal ENNReal
namespace SingularClosure.H12Frontier.Replay
noncomputable section

example : ∀ (cert : NonlinearCertificate)
    (ν : ℝ) (hν : 0 < ν) (a : CriticalSobolev 1) (ha : CriticalSigmaZero a)
    (hsmall : cert.constant * ‖a‖ < ν),
    ∃ U : CriticalRegularSolution ν a,
      (∀ T : ℝ, 0 < T → ∃ W : ℝ → CriticalSobolev 3,
        MemLp W 2 (volume.restrict (Icc (0 : ℝ) T)) ∧
        (∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T),
          criticalCoeff 3 (W t) = criticalCoeff 1 (U.critical t)) ∧
        (∫ t in Icc (0 : ℝ) T, ‖W t‖ ^ 2) ≤ (dissipationConstant cert) ν a) ∧
      (∀ T : ℝ, 0 < T → ∃ V : ℝ → CriticalSobolev (-1),
        MemLp V 2 (volume.restrict (Icc (0 : ℝ) T)) ∧
        (∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T),
          criticalCoeff (-1) (V t) = datumFourierCoeff (timeDerivative U.flow.velocity t)) ∧
        (∫ t in Icc (0 : ℝ) T, ‖V t‖ ^ 2) ≤ (derivativeConstant cert) ν a) ∧
      (∀ T : ℝ, 0 < T →
        IntegrableOn (fun t => physicalDissipation (U.flow.velocity t) ^ 2)
          (Icc (0 : ℝ) T) volume ∧
        (∫ t in (0 : ℝ)..T, physicalDissipation (U.flow.velocity t) ^ 2) ≤
          (‖a‖ ^ 4 - ‖U.critical T‖ ^ 4) /
            (4 * (ν - cert.constant * ‖a‖))) :=
  @SingularClosure.H12Frontier.Replay.quantitativeRegularity

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.H12Frontier.Replay.quantitativeRegularity"
#print axioms SingularClosure.H12Frontier.Replay.quantitativeRegularity

end
end SingularClosure.H12Frontier.Replay
