import SingularClosure.H12Frontier.ReplayDerivative
import SingularClosure.CriticalUniformBounds
import SingularClosure.CriticalTraceClosure

/-! Certificate-parametric replay. The registered fixed-coefficient milestone
is a separate specialization; this module does not assert that coefficient. -/
set_option autoImplicit false
set_option Elab.async true
open Set MeasureTheory Filter
open scoped BigOperators Topology Interval NNReal ENNReal
namespace SingularClosure.H12Frontier.Replay
noncomputable section

theorem stateNormBound (cert : NonlinearCertificate)
    {ν : ℝ} {N : ℕ} (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hsmall : cert.constant * ‖a‖ < ν)
    (g : GalerkinSolution ν (finiteSynthesis N (criticalCoeff 1 a)) N)
    {t : ℝ} (ht : 0 ≤ t) : ‖g.criticalState 1 t‖ ≤ ‖a‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg a)).mp
  have hnorm : ‖g.criticalState 1 t‖ ^ 2 = criticalEnergy 1 N (g.coeff t) := by
    rw [GalerkinSolution.criticalState, criticalFiniteSobolev_norm_sq]
    simp only [criticalEnergy, zpow_one, pow_one]
  rw [hnorm]
  exact (energyInvariant cert) a hreal hsmall ht g t ⟨ht, le_rfl⟩

def dissipationConstant (cert : NonlinearCertificate) (ν : ℝ) (a : CriticalSobolev 1) : ℝ :=
  ‖a‖ ^ 2 / (2 * (ν - cert.constant * ‖a‖))

def derivativeConstant (cert : NonlinearCertificate) (ν : ℝ) (a : CriticalSobolev 1) : ℝ :=
  (ν + criticalTransportConstant * ‖a‖) ^ 2 * ‖a‖ ^ 2 /
    (2 * (ν - cert.constant * ‖a‖))

theorem dissipationConstant_nonneg (cert : NonlinearCertificate)
    {ν : ℝ} (a : CriticalSobolev 1)
    (hsmall : cert.constant * ‖a‖ < ν) :
    0 ≤ (dissipationConstant cert) ν a :=
  div_nonneg (sq_nonneg _)
    (mul_nonneg (by norm_num) (sub_pos.mpr hsmall).le)

theorem derivativeConstant_nonneg (cert : NonlinearCertificate)
    {ν : ℝ} (a : CriticalSobolev 1)
    (hsmall : cert.constant * ‖a‖ < ν) :
    0 ≤ (derivativeConstant cert) ν a :=
  div_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    (mul_nonneg (by norm_num) (sub_pos.mpr hsmall).le)

theorem stateThreeIntegral (cert : NonlinearCertificate)
    {ν T : ℝ} {N : ℕ} (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hsmall : cert.constant * ‖a‖ < ν) (hT : 0 ≤ T)
    (g : GalerkinSolution ν (finiteSynthesis N (criticalCoeff 1 a)) N) :
    (∫ t in (0 : ℝ)..T, ‖g.criticalState 3 t‖ ^ 2) ≤ (dissipationConstant cert) ν a := by
  have h := (dissipationBudget cert) a hreal hsmall hT g T ⟨hT, le_rfl⟩
  have hnonneg := criticalEnergy_nonneg 1 N (g.coeff T)
  have hnorm (t : ℝ) : ‖g.criticalState 3 t‖ ^ 2 =
      criticalEnergy 3 N (g.coeff t) := by
    simpa only [Nat.cast_ofNat] using g.criticalState_norm_sq_nat 3 t
  simp_rw [hnorm]
  change (∫ t in (0 : ℝ)..T, criticalEnergy 3 N (g.coeff t)) ≤
    ‖a‖ ^ 2 / (2 * (ν - cert.constant * ‖a‖))
  apply (le_div_iff₀
    (mul_pos (by norm_num : (0 : ℝ) < 2) (sub_pos.mpr hsmall))).2
  nlinarith

theorem globalCompactness (cert : NonlinearCertificate)
    (ν : ℝ) (hν : 0 ≤ ν) (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hsol : SpectralSolenoidal (criticalCoeff 1 a))
    (hsmall : cert.constant * ‖a‖ < ν) :
    ∃ u : ℝ → CriticalSobolev 1, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      (∀ t, 0 ≤ t → ‖u t‖ ≤ ‖a‖) ∧
      ContinuousOn (fun t => criticalToTorusH0 1 (by norm_num) (u t)) (Ici 0) ∧
      (∀ T : ℝ, TendstoUniformlyOn
        (fun n t => (criticalDatumGalerkinFamily ν hν a hreal hsol (φ n)).sobolevState 0 t)
        (fun t => criticalToTorusH0 1 (by norm_num) (u t)) atTop (Icc (0 : ℝ) T)) ∧
      ∀ T : ℝ, 0 ≤ T → ∃ u1 : TimeH1L2 T,
        Tendsto
          (fun n => (criticalDatumGalerkinFamily ν hν a hreal hsol (φ n)).criticalTimeH1L2 T)
          atTop (𝓝 u1) := by
  apply CRITICAL_GALERKIN_GLOBAL_COMPACTNESS ν
    (fun n => finiteSynthesis (n + 1) (criticalCoeff 1 a)) (fun n => n + 1)
    (criticalDatumGalerkinFamily ν hν a hreal hsol)
    ‖a‖ ((dissipationConstant cert) ν a) ((derivativeConstant cert) ν a)
    (norm_nonneg a) ((dissipationConstant_nonneg cert) a hsmall)
    ((derivativeConstant_nonneg cert) a hsmall)
  · intro n t ht
    exact (stateNormBound cert) a hreal hsmall _ ht
  · intro n T hT
    exact (stateThreeIntegral cert) a hreal hsmall hT _
  · intro n T hT
    exact (timeDerivativeBudget cert) hν a hreal hsmall hT _

end
end SingularClosure.H12Frontier.Replay
