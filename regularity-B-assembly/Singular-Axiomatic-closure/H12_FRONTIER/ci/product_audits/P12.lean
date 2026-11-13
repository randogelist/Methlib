import SingularClosure.H12Frontier.ProductMilestones

set_option autoImplicit false
set_option Elab.async false
open Set MeasureTheory Filter
open scoped BigOperators Topology Interval NNReal ENNReal
namespace SingularClosure.H12Frontier
noncomputable section

example :
    ∀ (ν : ℝ) (hν : 0 ≤ ν) (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hsmall : nativeProduct * ‖a‖ < ν)
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
      (∫ t in Icc (0 : ℝ) T, ‖V t‖ ^ 2) ≤ (Replay.derivativeConstant nativeProductCertificate) ν a :=
  @SingularClosure.H12Frontier.PRODUCT_LIMIT_NEGATIVE_HALF

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.H12Frontier.PRODUCT_LIMIT_NEGATIVE_HALF"
#print axioms SingularClosure.H12Frontier.PRODUCT_LIMIT_NEGATIVE_HALF

example :
    ∀ (ν : ℝ) (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hsmall : nativeProduct * ‖a‖ < ν)
    (φ : ℕ → ℕ)
    (g : ∀ n, GalerkinSolution ν
      (finiteSynthesis (φ n + 1) (criticalCoeff 1 a)) (φ n + 1))
    (u : ℝ → CriticalSobolev 1) (T : ℝ) (hT : 0 ≤ T)
    (hconv : TendstoUniformlyOn (fun n t => (g n).sobolevState 0 t)
      (fun t => criticalToTorusH0 1 (by norm_num) (u t)) atTop (Icc (0 : ℝ) T)),
    ENNReal.ofReal (‖u T‖ ^ 4) +
      ENNReal.ofReal (4 * (ν - nativeProduct * ‖a‖)) *
        (∫⁻ t in Icc (0 : ℝ) T,
          criticalExtendedSquare 2 (criticalCoeff 1 (u t)) ^ 2) ≤ ENNReal.ofReal (‖a‖ ^ 4) :=
  @SingularClosure.H12Frontier.PRODUCT_LIMIT_QUARTIC

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.H12Frontier.PRODUCT_LIMIT_QUARTIC"
#print axioms SingularClosure.H12Frontier.PRODUCT_LIMIT_QUARTIC

example :
    ∀ (ν : ℝ) (hν : 0 ≤ ν) (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hsmall : nativeProduct * ‖a‖ < ν)
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
      (∫ t in Icc (0 : ℝ) T, ‖V t‖ ^ 2) ≤ (Replay.derivativeConstant nativeProductCertificate) ν a :=
  @SingularClosure.H12Frontier.PRODUCT_PHYSICAL_NEGATIVE_HALF

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.H12Frontier.PRODUCT_PHYSICAL_NEGATIVE_HALF"
#print axioms SingularClosure.H12Frontier.PRODUCT_PHYSICAL_NEGATIVE_HALF

example :
    ∀ (ν : ℝ) (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hsmall : nativeProduct * ‖a‖ < ν)
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
        (‖a‖ ^ 4 - ‖u T‖ ^ 4) / (4 * (ν - nativeProduct * ‖a‖)) :=
  @SingularClosure.H12Frontier.PRODUCT_PHYSICAL_QUARTIC

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.H12Frontier.PRODUCT_PHYSICAL_QUARTIC"
#print axioms SingularClosure.H12Frontier.PRODUCT_PHYSICAL_QUARTIC

example :
    ∀ (ν : ℝ) (hν : 0 < ν) (a : CriticalSobolev 1) (ha : CriticalSigmaZero a)
    (hsmall : nativeProduct * ‖a‖ < ν),
    ∃ U : CriticalRegularSolution ν a,
      (∀ T : ℝ, 0 < T → ∃ W : ℝ → CriticalSobolev 3,
        MemLp W 2 (volume.restrict (Icc (0 : ℝ) T)) ∧
        (∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T),
          criticalCoeff 3 (W t) = criticalCoeff 1 (U.critical t)) ∧
        (∫ t in Icc (0 : ℝ) T, ‖W t‖ ^ 2) ≤ (Replay.dissipationConstant nativeProductCertificate) ν a) ∧
      (∀ T : ℝ, 0 < T → ∃ V : ℝ → CriticalSobolev (-1),
        MemLp V 2 (volume.restrict (Icc (0 : ℝ) T)) ∧
        (∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T),
          criticalCoeff (-1) (V t) = datumFourierCoeff (timeDerivative U.flow.velocity t)) ∧
        (∫ t in Icc (0 : ℝ) T, ‖V t‖ ^ 2) ≤ (Replay.derivativeConstant nativeProductCertificate) ν a) ∧
      (∀ T : ℝ, 0 < T →
        IntegrableOn (fun t => physicalDissipation (U.flow.velocity t) ^ 2)
          (Icc (0 : ℝ) T) volume ∧
        (∫ t in (0 : ℝ)..T, physicalDissipation (U.flow.velocity t) ^ 2) ≤
          (‖a‖ ^ 4 - ‖U.critical T‖ ^ 4) /
            (4 * (ν - nativeProduct * ‖a‖))) :=
  @SingularClosure.H12Frontier.PRODUCT_QUANTITATIVE_REGULARITY

#eval IO.println "EXACT_TYPE_PASS:SingularClosure.H12Frontier.PRODUCT_QUANTITATIVE_REGULARITY"
#print axioms SingularClosure.H12Frontier.PRODUCT_QUANTITATIVE_REGULARITY

end
end SingularClosure.H12Frontier
