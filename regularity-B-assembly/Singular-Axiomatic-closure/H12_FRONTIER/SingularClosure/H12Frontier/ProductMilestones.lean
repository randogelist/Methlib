import SingularClosure.H12Frontier.ExplicitNonlinear
import SingularClosure.H12Frontier.ReplayClosure

/-! Product-certificate checkpoints P06-P14. Explicit types preserve the
registered datum and Galerkin hypotheses; finite/limit integrals retain their
original real or ENNReal codomains. Compilation and axiom audit are external. -/
set_option autoImplicit false
set_option Elab.async true
open Set MeasureTheory Filter
open scoped BigOperators Topology Interval NNReal ENNReal
namespace SingularClosure.H12Frontier
noncomputable section

/-- P06: specialization of `Replay.differentialInequality`. -/
theorem PRODUCT_GALERKIN_DIFFERENTIAL_INEQUALITY :
    ∀ {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N)
    {t : ℝ} (ht : 0 ≤ t),
    criticalEnergyRate ν 1 N (g.coeff t) +
      2 * (ν - nativeProduct * Real.sqrt (criticalEnergy 1 N (g.coeff t))) *
        criticalEnergy 3 N (g.coeff t) ≤ 0 :=
  @Replay.differentialInequality nativeProductCertificate

/-- P07: specialization of `Replay.energyInvariant`. -/
theorem PRODUCT_GALERKIN_ENERGY_INVARIANT :
    ∀ {ν T : ℝ} {N : ℕ} (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hsmall : nativeProduct * ‖a‖ < ν) (hT : 0 ≤ T)
    (g : GalerkinSolution ν (finiteSynthesis N (criticalCoeff 1 a)) N),
    ∀ t ∈ Icc 0 T, criticalEnergy 1 N (g.coeff t) ≤ ‖a‖ ^ 2 :=
  @Replay.energyInvariant nativeProductCertificate

/-- P07: specialization of `Replay.dissipationBudget`. -/
theorem PRODUCT_GALERKIN_DISSIPATION_BUDGET :
    ∀ {ν T : ℝ} {N : ℕ} (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hsmall : nativeProduct * ‖a‖ < ν) (hT : 0 ≤ T)
    (g : GalerkinSolution ν (finiteSynthesis N (criticalCoeff 1 a)) N),
    ∀ t ∈ Icc 0 T,
      criticalEnergy 1 N (g.coeff t) + 2 * (ν - nativeProduct * ‖a‖) *
        (∫ s in (0 : ℝ)..t, criticalEnergy 3 N (g.coeff s)) ≤ ‖a‖ ^ 2 :=
  @Replay.dissipationBudget nativeProductCertificate

/-- P07: specialization of `Replay.stateNormBound`. -/
theorem PRODUCT_GALERKIN_STATE_NORM_BOUND :
    ∀ {ν : ℝ} {N : ℕ} (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hsmall : nativeProduct * ‖a‖ < ν)
    (g : GalerkinSolution ν (finiteSynthesis N (criticalCoeff 1 a)) N)
    {t : ℝ} (ht : 0 ≤ t),
    ‖g.criticalState 1 t‖ ≤ ‖a‖ :=
  @Replay.stateNormBound nativeProductCertificate

/-- P07: specialization of `Replay.stateThreeIntegral`. -/
theorem PRODUCT_GALERKIN_STATE_THREE_INTEGRAL :
    ∀ {ν T : ℝ} {N : ℕ} (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hsmall : nativeProduct * ‖a‖ < ν) (hT : 0 ≤ T)
    (g : GalerkinSolution ν (finiteSynthesis N (criticalCoeff 1 a)) N),
    (∫ t in (0 : ℝ)..T, ‖g.criticalState 3 t‖ ^ 2) ≤ (Replay.dissipationConstant nativeProductCertificate) ν a :=
  @Replay.stateThreeIntegral nativeProductCertificate

/-- P08: specialization of `Replay.sharpSquareBudget`. -/
theorem PRODUCT_GALERKIN_SHARP_QUARTIC :
    ∀ {ν T : ℝ} {N : ℕ} (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hsmall : nativeProduct * ‖a‖ < ν) (hT : 0 ≤ T)
    (g : GalerkinSolution ν (finiteSynthesis N (criticalCoeff 1 a)) N),
    (∫ t in (0 : ℝ)..T, coefficientDissipation N (g.coeff t) ^ 2) ≤
      (‖a‖ ^ 4 - criticalEnergy 1 N (g.coeff T) ^ 2) /
        (4 * (ν - nativeProduct * ‖a‖)) :=
  @Replay.sharpSquareBudget nativeProductCertificate

/-- P09: specialization of `Replay.sixChannelBudget`. -/
theorem PRODUCT_SIX_CHANNEL_BUDGET :
    ∀ {ν T : ℝ} {N : ℕ} (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hsmall : nativeProduct * ‖a‖ < ν) (hT : 0 ≤ T)
    (g : GalerkinSolution ν (finiteSynthesis N (criticalCoeff 1 a)) N),
    budget6 N g.coeff T ≤
      ENNReal.ofReal (‖a‖ ^ 4 / (4 * (ν - nativeProduct * ‖a‖))) :=
  @Replay.sixChannelBudget nativeProductCertificate

/-- P09: specialization of `Replay.datumAX6`. -/
theorem PRODUCT_DATUM_AX6 :
    ∀ (ν : ℝ) (_hν : 0 < ν) (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (_hsol : SpectralSolenoidal (criticalCoeff 1 a))
    (_hzero : SpectralMeanZero (criticalCoeff 1 a))
    (hsmall : nativeProduct * ‖a‖ < ν),
    CriticalDatumAX6 ν a :=
  @Replay.datumAX6 nativeProductCertificate

/-- P10: specialization of `Replay.timeDerivativePointwise`. -/
theorem PRODUCT_TIME_DERIVATIVE_POINTWISE :
    ∀ {ν T : ℝ} {N : ℕ} (hν : 0 ≤ ν) (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hsmall : nativeProduct * ‖a‖ < ν) (hT : 0 ≤ T)
    (g : GalerkinSolution ν (finiteSynthesis N (criticalCoeff 1 a)) N)
    {t : ℝ} (ht : t ∈ Icc 0 T),
    ‖g.criticalRhs (-1) t‖ ≤
      (ν + criticalTransportConstant * ‖a‖) * Real.sqrt (criticalEnergy 3 N (g.coeff t)) :=
  @Replay.timeDerivativePointwise nativeProductCertificate

/-- P10: specialization of `Replay.timeDerivativeSquare`. -/
theorem PRODUCT_TIME_DERIVATIVE_SQUARE :
    ∀ {ν T : ℝ} {N : ℕ} (hν : 0 ≤ ν) (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hsmall : nativeProduct * ‖a‖ < ν) (hT : 0 ≤ T)
    (g : GalerkinSolution ν (finiteSynthesis N (criticalCoeff 1 a)) N)
    {t : ℝ} (ht : t ∈ Icc 0 T),
    ‖g.criticalRhs (-1) t‖ ^ 2 ≤
      (ν + criticalTransportConstant * ‖a‖) ^ 2 * criticalEnergy 3 N (g.coeff t) :=
  @Replay.timeDerivativeSquare nativeProductCertificate

/-- P10: specialization of `Replay.timeDerivativeBudget`. -/
theorem PRODUCT_TIME_DERIVATIVE_BUDGET :
    ∀ {ν T : ℝ} {N : ℕ} (hν : 0 ≤ ν) (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hsmall : nativeProduct * ‖a‖ < ν) (hT : 0 ≤ T)
    (g : GalerkinSolution ν (finiteSynthesis N (criticalCoeff 1 a)) N),
    (∫ t in (0 : ℝ)..T, ‖g.criticalRhs (-1) t‖ ^ 2) ≤
      (ν + criticalTransportConstant * ‖a‖) ^ 2 * ‖a‖ ^ 2 /
        (2 * (ν - nativeProduct * ‖a‖)) :=
  @Replay.timeDerivativeBudget nativeProductCertificate

/-- P11: specialization of `Replay.globalCompactness`. -/
theorem PRODUCT_GLOBAL_COMPACTNESS :
    ∀ (ν : ℝ) (hν : 0 ≤ ν) (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hsol : SpectralSolenoidal (criticalCoeff 1 a))
    (hsmall : nativeProduct * ‖a‖ < ν),
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
  @Replay.globalCompactness nativeProductCertificate

/-- P11: specialization of `Replay.positiveEnstrophy`. -/
theorem PRODUCT_POSITIVE_ENSTROPHY :
    ∀ (ν : ℝ) (hν : 0 < ν) (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hsmall : nativeProduct * ‖a‖ < ν)
    (τ : ℝ) (hτ : 0 < τ) (T : ℝ) (hτT : τ ≤ T),
    ∃ L : ℝ, 0 ≤ L ∧ ∀ N : ℕ,
      ∀ g : GalerkinSolution ν (finiteSynthesis N (criticalCoeff 1 a)) N,
      ∀ t ∈ Icc τ T,
        coefficientDissipation N (g.coeff t) +
          ν * (∫ s in τ..t, coefficientLaplacianSquare N (g.coeff s)) ≤ L :=
  @Replay.positiveEnstrophy nativeProductCertificate

/-- P11: specialization of `Replay.positiveH2`. -/
theorem PRODUCT_POSITIVE_H2 :
    ∀ (ν : ℝ) (hν : 0 < ν) (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hsmall : nativeProduct * ‖a‖ < ν)
    (τ : ℝ) (hτ : 0 < τ) (T : ℝ) (hτT : τ ≤ T),
    ∃ S : ℝ, 0 ≤ S ∧ ∀ N : ℕ,
      ∀ g : GalerkinSolution ν (finiteSynthesis N (criticalCoeff 1 a)) N,
        (∫ t in τ..T, highOrderEnergy 2 N (g.coeff t)) ≤ S :=
  @Replay.positiveH2 nativeProductCertificate

/-- P11: specialization of `Replay.positiveAllOrders`. -/
theorem PRODUCT_POSITIVE_ALL_ORDERS :
    ∀ (ν : ℝ) (hν : 0 < ν) (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hsmall : nativeProduct * ‖a‖ < ν)
    (m : ℕ) (τ T : ℝ) (hτ : 0 < τ) (hτT : τ < T),
    ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ,
      ∀ g : GalerkinSolution ν (finiteSynthesis N (criticalCoeff 1 a)) N,
      ∀ t ∈ Icc τ T, highOrderEnergy m N (g.coeff t) +
        ν * (∫ s in τ..t, highOrderEnergy (m + 1) N (g.coeff s)) ≤ B :=
  @Replay.positiveAllOrders nativeProductCertificate

/-- P11: specialization of `Replay.positiveFlow`. -/
theorem PRODUCT_POSITIVE_FLOW :
    ∀ (ν : ℝ) (hν : 0 < ν) (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hsmall : nativeProduct * ‖a‖ < ν)
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (g : ∀ n : ℕ, GalerkinSolution ν
      (finiteSynthesis (φ n + 1) (criticalCoeff 1 a)) (φ n + 1))
    (u : ℝ → TorusSobolev 0) (hu : ContinuousOn u (Ici 0))
    (hconv : ∀ T : ℝ, 0 < T → TendstoUniformlyOn
      (fun n t => (g n).sobolevState 0 t) u atTop (Icc (0 : ℝ) T)),
    ∃ L : CriticalPositiveSobolevFlow ν, ∀ t : ℝ, 0 < t → L.state 0 t = u t :=
  @Replay.positiveFlow nativeProductCertificate

/-- P12: specialization of `Replay.limitNegativeHalf`. -/
theorem PRODUCT_LIMIT_NEGATIVE_HALF :
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
  @Replay.limitNegativeHalf nativeProductCertificate

/-- P12: specialization of `Replay.limitQuartic`. -/
theorem PRODUCT_LIMIT_QUARTIC :
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
  @Replay.limitQuartic nativeProductCertificate

/-- P12: specialization of `Replay.physicalNegativeHalf`. -/
theorem PRODUCT_PHYSICAL_NEGATIVE_HALF :
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
  @Replay.physicalNegativeHalf nativeProductCertificate

/-- P12: specialization of `Replay.physicalQuartic`. -/
theorem PRODUCT_PHYSICAL_QUARTIC :
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
  @Replay.physicalQuartic nativeProductCertificate

/-- P12: specialization of `Replay.quantitativeRegularity`. -/
theorem PRODUCT_QUANTITATIVE_REGULARITY :
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
  @Replay.quantitativeRegularity nativeProductCertificate

/-- P13: specialization of `Replay.globalEnergyClass`. -/
theorem PRODUCT_GLOBAL_ENERGY_CLASS :
    ∀ (ν : ℝ) (hν : 0 < ν) (a : CriticalSobolev 1) (ha : CriticalSigmaZero a)
    (hsmall : nativeProduct * ‖a‖ < ν),
    ∃ U : CriticalRegularSolution ν a,
      (MemLp U.flow.threeHalfState 2 (volume.restrict (Ioi (0 : ℝ))) ∧
        (∫ t in Ioi (0 : ℝ), ‖U.flow.threeHalfState t‖ ^ 2) ≤ (Replay.dissipationConstant nativeProductCertificate) ν a) ∧
      (MemLp U.flow.negativeHalfDerivative 2 (volume.restrict (Ioi (0 : ℝ))) ∧
        (∫ t in Ioi (0 : ℝ), ‖U.flow.negativeHalfDerivative t‖ ^ 2) ≤
          (Replay.derivativeConstant nativeProductCertificate) ν a) ∧
      (∀ T : ℝ, 0 < T →
        IntegrableOn (fun t => physicalDissipation (U.flow.velocity t) ^ 2)
          (Icc (0 : ℝ) T) volume ∧
        (∫ t in (0 : ℝ)..T, physicalDissipation (U.flow.velocity t) ^ 2) ≤
          (‖a‖ ^ 4 - ‖U.critical T‖ ^ 4) /
            (4 * (ν - nativeProduct * ‖a‖))) :=
  @Replay.globalEnergyClass nativeProductCertificate

/-- P08: the undivided square budget preserves the actual initial energy. -/
theorem PRODUCT_GALERKIN_SQUARE_BUDGET :
    ∀ {ν T : ℝ} {N : ℕ} (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hsmall : nativeProduct * ‖a‖ < ν) (hT : 0 ≤ T)
    (g : GalerkinSolution ν (finiteSynthesis N (criticalCoeff 1 a)) N),
    ∀ t ∈ Icc 0 T,
      criticalEnergy 1 N (g.coeff t) ^ 2 +
        4 * (ν - nativeProduct * ‖a‖) *
          (∫ s in (0 : ℝ)..t, criticalEnergy 2 N (g.coeff s) ^ 2) ≤
        criticalEnergy 1 N (g.coeff 0) ^ 2 := by
  intro ν T N a hreal hsmall hT g
  exact CRITICAL_SQUARE_BUDGET hT nativeProduct_pos.le (norm_nonneg a) hsmall
    ((g.criticalEnergy_continuousOn 1).mono (fun t ht => ht.1))
    ((g.criticalEnergy_continuousOn 2).mono (fun t ht => ht.1))
    (fun t _ => criticalEnergy_nonneg 1 N (g.coeff t))
    (fun t _ => criticalEnergy_nonneg 3 N (g.coeff t))
    (criticalGalerkin_criticalEnergy_initial_le 1 a hreal g)
    (fun t ht => g.criticalEnergy_balance 1 ht.1)
    (fun t ht => PRODUCT_GALERKIN_DIFFERENTIAL_INEQUALITY g ht.1)
    (fun t _ => criticalEnergy_interpolation N (g.coeff t))

/-- P14: the same solution inherits the Serrin, Leray-Hopf, uniqueness and
physical NSE conclusions from its product quartic budget. -/
theorem PRODUCT_SERRIN_LERAYHOPF
    (ν : ℝ) (hν : 0 < ν) (a : CriticalSobolev 1)
    (hsmall : nativeProduct * ‖a‖ < ν)
    (U : CriticalRegularSolution ν a)
    (hQ : ∀ T : ℝ, 0 < T →
      IntegrableOn (fun t => physicalDissipation (U.flow.velocity t) ^ 2)
        (Icc (0 : ℝ) T) volume ∧
      (∫ t in (0 : ℝ)..T, physicalDissipation (U.flow.velocity t) ^ 2) ≤
        (‖a‖ ^ 4 - ‖U.critical T‖ ^ 4) /
          (4 * (ν - nativeProduct * ‖a‖))) :
    CriticalLerayHopf ν (criticalInitialPhysicalL2 a) U.lerayVelocity U.lerayGradient ∧
    U.lerayHopfUnique ∧
    PositiveSmoothNSE ν U.flow.velocity U.flow.pressure ∧
    MemLp (fun t => criticalSpatialNorm 6 (U.flow.velocity t)) 4
      (volume.restrict (Ioi (0 : ℝ))) := by
  have hδ : 0 < ν - nativeProduct * ‖a‖ := sub_pos.mpr hsmall
  have hM : 0 ≤ ‖a‖ ^ 4 / (4 * (ν - nativeProduct * ‖a‖)) :=
    div_nonneg (by positivity) (by positivity)
  have hS := U.serrin_global_memLp_of_quartic_budget
    (‖a‖ ^ 4 / (4 * (ν - nativeProduct * ‖a‖))) hM
    (fun T hT => ⟨(hQ T hT).1, (hQ T hT).2.trans
      (div_le_div_of_nonneg_right (sub_le_self _ (by positivity)) (by positivity))⟩)
  have hSloc (T : ℝ) (hT : 0 < T) :
      MemLp (fun t => criticalSpatialNorm 6 (U.flow.velocity t)) 4
        (volume.restrict (Ioc (0 : ℝ) T)) :=
    U.serrin_time_memLp T (hQ T hT).1
  exact ⟨U.lerayHopf_of_quartic (fun T hT => (hQ T hT).1),
    U.lerayHopfUnique_of_serrin hν hSloc, U.physicalNSE, hS.1⟩

end
end SingularClosure.H12Frontier
