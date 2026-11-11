import SingularClosure.GlobalSobolevTrace
import SingularClosure.CanonicalRhsSobolev
import SingularClosure.TransportLimit
import SingularClosure.FourierProduct
import SingularClosure.PeriodicFourierInjective

/-!
# Frozen endpoint 8: the actual global Galerkin strong limit

One increasing canonical cutoff subsequence converges uniformly on every
finite time interval in every integral Sobolev order. The limit has the actual
Hilbert-valued time derivative, the physical initial coefficients, and all
Fourier state constraints. The nonlinear limit is the literal untruncated
transport, identified with the Fourier coefficients of physical convection.
No higher temporal smoothness or physical-equation adapter is assumed.
-/

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Topology ENNReal Interval

namespace SingularClosure

noncomputable section

structure GlobalGalerkinStrongLimit (ν : ℝ) (a : Field) (ha : SmoothSigmaZero a) where
  viscosity_pos : 0 < ν
  state : ∀ r : ℕ, ℝ → TorusSobolev r
  rhs : ∀ r : ℕ, ℝ → TorusSobolev r
  subsequence : ℕ → ℕ
  subsequence_strict : StrictMono subsequence
  state_continuous : ∀ r : ℕ, ContinuousOn (state r) (Ici 0)
  rhs_continuous : ∀ r : ℕ, ContinuousOn (rhs r) (Ici 0)
  state_inclusion : ∀ (r : ℕ) (t : ℝ), 0 ≤ t →
    torusSobolevInclusion r (state (r + 1) t) = state r t
  rhs_inclusion : ∀ (r : ℕ) (t : ℝ), 0 ≤ t →
    torusSobolevInclusion r (rhs (r + 1) t) = rhs r t
  state_derivative : ∀ (r : ℕ) (t : ℝ), 0 ≤ t →
    HasDerivWithinAt (state r) (rhs r t) (Ici 0) t
  rhs_coeff : ∀ (r : ℕ) (t : ℝ), 0 ≤ t →
    (rhs r t).val = fullFourierRhs ν (state 0 t)
  initial : ∀ r : ℕ, state r 0 = smoothDatumSobolev r a ha.smooth ha.periodic
  reality : ∀ (r : ℕ) (t : ℝ), 0 ≤ t → SpectralReality (state r t).val
  solenoidal : ∀ (r : ℕ) (t : ℝ), 0 ≤ t → SpectralSolenoidal (state r t).val
  mean_zero : ∀ (r : ℕ) (t : ℝ), 0 ≤ t → SpectralMeanZero (state r t).val
  canonical_uniform : ∀ (T : ℝ) (r : ℕ), TendstoUniformlyOn
    (fun n t => (canonicalGalerkinSolution ν viscosity_pos a ha
      (subsequence n + 1)).sobolevState r t)
    (state r) atTop (Icc (0 : ℝ) T)
  transport_uniform : ∀ (T : ℝ) (k : Frequency) (i : Fin 3), TendstoUniformlyOn
    (fun n t => coefficientTransport (subsequence n + 1)
      ((canonicalGalerkinSolution ν viscosity_pos a ha (subsequence n + 1)).coeff t) k i)
    (fun t => fullTransportCoefficients (state 0 t) k i) atTop (Icc (0 : ℝ) T)
  physical_convection_coeff : ∀ t : ℝ, 0 ≤ t →
    datumFourierCoeff (convection (smoothFourierSynthesis (state 0 t).val)) =
      fullTransportCoefficients (state 0 t)

/-- Every Sobolev order of the actual limit represents the same H0 coefficients. -/
theorem GlobalGalerkinStrongLimit.state_coeff_eq_zero
    {ν : ℝ} {a : Field} {ha : SmoothSigmaZero a} (L : GlobalGalerkinStrongLimit ν a ha)
    (r : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    (L.state r t).val = (L.state 0 t).val :=
  globalSobolevCurves_coeff_eq_H0 L.state L.state_inclusion r t ht

theorem GlobalGalerkinStrongLimit.rhs_coeff_eq_zero
    {ν : ℝ} {a : Field} {ha : SmoothSigmaZero a} (L : GlobalGalerkinStrongLimit ν a ha)
    (r : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    (L.rhs r t).val = (L.rhs 0 t).val :=
  globalSobolevCurves_coeff_eq_H0 L.rhs L.rhs_inclusion r t ht

theorem GlobalGalerkinStrongLimit.state_all_mem
    {ν : ℝ} {a : Field} {ha : SmoothSigmaZero a} (L : GlobalGalerkinStrongLimit ν a ha)
    (t : ℝ) (ht : 0 ≤ t) (r : ℕ) :
    Memℓp (sobolevWeightedCoeff r (L.state 0 t).val) 2 :=
  globalSobolevCurves_all_mem L.state L.state_inclusion t ht r

theorem GlobalGalerkinStrongLimit.rhs_all_mem
    {ν : ℝ} {a : Field} {ha : SmoothSigmaZero a} (L : GlobalGalerkinStrongLimit ν a ha)
    (t : ℝ) (ht : 0 ≤ t) (r : ℕ) :
    Memℓp (sobolevWeightedCoeff r (L.rhs 0 t).val) 2 :=
  globalSobolevCurves_all_mem L.rhs L.rhs_inclusion t ht r

theorem GlobalGalerkinStrongLimit.state_memLp
    {ν : ℝ} {a : Field} {ha : SmoothSigmaZero a} (L : GlobalGalerkinStrongLimit ν a ha)
    (r : ℕ) (T : ℝ) (p : ℝ≥0∞) :
    MemLp (L.state r) p (volume.restrict (Icc (0 : ℝ) T)) :=
  torusSobolev_memLp_Icc_of_continuousOn r (L.state r) T p
    ((L.state_continuous r).mono (fun t ht => ht.1))

theorem GlobalGalerkinStrongLimit.rhs_memLp
    {ν : ℝ} {a : Field} {ha : SmoothSigmaZero a} (L : GlobalGalerkinStrongLimit ν a ha)
    (r : ℕ) (T : ℝ) (p : ℝ≥0∞) :
    MemLp (L.rhs r) p (volume.restrict (Icc (0 : ℝ) T)) :=
  torusSobolev_memLp_Icc_of_continuousOn r (L.rhs r) T p
    ((L.rhs_continuous r).mono (fun t ht => ht.1))

theorem GlobalGalerkinStrongLimit.state_integral_rhs
    {ν : ℝ} {a : Field} {ha : SmoothSigmaZero a} (L : GlobalGalerkinStrongLimit ν a ha)
    (r : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    (∫ z in (0 : ℝ)..t, L.rhs r z) = L.state r t - L.state r 0 := by
  have hu : ContinuousOn (L.state r) (Icc (0 : ℝ) t) :=
    (L.state_continuous r).mono (fun z hz => hz.1)
  have hr : ContinuousOn (L.rhs r) (Icc (0 : ℝ) t) :=
    (L.rhs_continuous r).mono (fun z hz => hz.1)
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht hu
    _ (hr.intervalIntegrable_of_Icc ht)
  intro z hz
  exact (L.state_derivative r z hz.1.le).hasDerivAt (Ici_mem_nhds hz.1)

theorem GlobalGalerkinStrongLimit.state_time_integral
    {ν : ℝ} {a : Field} {ha : SmoothSigmaZero a} (L : GlobalGalerkinStrongLimit ν a ha)
    (r : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    L.state r t = L.state r 0 + ∫ z in (0 : ℝ)..t, L.rhs r z := by
  rw [L.state_integral_rhs r t ht]
  abel

/-- Literal physical velocity of the global strong Galerkin limit. -/
def GlobalGalerkinStrongLimit.velocity
    {ν : ℝ} {a : Field} {ha : SmoothSigmaZero a} (L : GlobalGalerkinStrongLimit ν a ha) :
    Velocity := fun t => smoothFourierSynthesis (L.state 0 t).val

theorem GlobalGalerkinStrongLimit.velocity_smoothSigmaZero
    {ν : ℝ} {a : Field} {ha : SmoothSigmaZero a} (L : GlobalGalerkinStrongLimit ν a ha)
    (t : ℝ) (ht : 0 ≤ t) : SmoothSigmaZero (L.velocity t) :=
  smoothFourierSynthesis_smoothSigmaZero (L.state 0 t).val (L.state_all_mem t ht)
    (L.mean_zero 0 t ht) (L.solenoidal 0 t ht)

theorem GlobalGalerkinStrongLimit.velocity_initial
    {ν : ℝ} {a : Field} {ha : SmoothSigmaZero a} (L : GlobalGalerkinStrongLimit ν a ha) :
    L.velocity 0 = a := by
  have hv := L.velocity_smoothSigmaZero 0 le_rfl
  apply datumFourierCoeff_injective_continuous_periodic (L.velocity 0) a
    hv.smooth.continuous ha.smooth.continuous hv.periodic ha.periodic
  change datumFourierCoeff (smoothFourierSynthesis (L.state 0 0).val) = datumFourierCoeff a
  rw [datumFourierCoeff_smoothFourierSynthesis _
    (ALL_SOBOLEV_IMP_RAPID_SCALAR _ (L.state_all_mem 0 le_rfl)) (L.reality 0 0 le_rfl),
    L.initial 0]
  rfl

/-- Frozen endpoint 8, with actual canonical convergence, the untruncated
Hilbert equation, and the literal physical nonlinear coefficient identity. -/
theorem GALERKIN_GLOBAL_STRONG_LIMIT (hAX6 : AX6Statement)
    (ν : ℝ) (hν : 0 < ν) (a : Field) (ha : SmoothSigmaZero a) :
    Nonempty (GlobalGalerkinStrongLimit ν a ha) := by
  obtain ⟨U, φ, hφ, hU, hinc, hconv, hinitial, hconstraints⟩ :=
    AX6_CANONICAL_GALERKIN_GLOBAL_SOBOLEV_TRACE hAX6 ν hν a ha
  have hconv0 : ∀ T : ℝ, 0 < T → TendstoUniformlyOn
      (fun n t => (canonicalGalerkinSolution ν hν a ha (φ n + 1)).sobolevState 0 t)
      (U 0) atTop (Icc (0 : ℝ) T) := fun T _ => hconv T 0
  let R := canonicalLimitRhsSobolev hAX6 ν hν a ha (U 0) φ hφ hconv0
  refine ⟨{
    viscosity_pos := hν
    state := U
    rhs := R
    subsequence := φ
    subsequence_strict := hφ
    state_continuous := hU
    rhs_continuous := ?_
    state_inclusion := hinc
    rhs_inclusion := ?_
    state_derivative := ?_
    rhs_coeff := ?_
    initial := hinitial
    reality := fun r t ht => (hconstraints r t ht).1
    solenoidal := fun r t ht => (hconstraints r t ht).2.1
    mean_zero := fun r t ht => (hconstraints r t ht).2.2
    canonical_uniform := hconv
    transport_uniform := ?_
    physical_convection_coeff := ?_
  }⟩
  · intro r
    exact canonicalLimitRhsSobolev_continuousOn
      hAX6 ν hν a ha (U 0) φ hφ hconv0 (hU 0) r
  · intro r t ht
    exact canonicalLimitRhsSobolev_inclusion hAX6 ν hν a ha (U 0) φ hφ hconv0 r t ht
  · intro r t ht
    exact canonicalLimitRhsSobolev_hasDerivWithinAt_order
      hAX6 ν hν a ha (U 0) φ hφ hconv0 (hU 0) r (U r)
      (globalSobolevCurves_coeff_eq_H0 U hinc r) t ht
  · intro r t ht
    exact canonicalLimitRhsSobolev_coeff hAX6 ν hν a ha (U 0) φ hφ hconv0 r t ht
  · intro T k i
    exact galerkinLimit_transport_tendstoUniformlyOn ν a φ
      (fun n => canonicalGalerkinSolution ν hν a ha (φ n + 1)) T (U 0)
      ((hU 0).mono (fun t ht => ht.1)) (hconv T 0) k i
  · intro t ht
    exact smoothFourierSynthesis_convection_coeff (U 0 t)
      (globalSobolevCurves_all_mem U hinc t ht)
      (hconstraints 0 t ht).1 (hconstraints 0 t ht).2.1

end

end SingularClosure
