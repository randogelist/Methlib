import SingularClosure.H12Frontier.ReplayEnergy
import SingularClosure.CriticalTimeDerivative

/-! Certificate-parametric replay. The registered fixed-coefficient milestone
is a separate specialization; this module does not assert that coefficient. -/
set_option autoImplicit false
set_option Elab.async true
open Set MeasureTheory Filter
open scoped BigOperators Topology Interval NNReal ENNReal
namespace SingularClosure.H12Frontier.Replay
noncomputable section

theorem timeDerivativePointwise (cert : NonlinearCertificate)
    {ν T : ℝ} {N : ℕ} (hν : 0 ≤ ν) (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hsmall : cert.constant * ‖a‖ < ν) (hT : 0 ≤ T)
    (g : GalerkinSolution ν (finiteSynthesis N (criticalCoeff 1 a)) N)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖g.criticalRhs (-1) t‖ ≤
      (ν + criticalTransportConstant * ‖a‖) * Real.sqrt (criticalEnergy 3 N (g.coeff t)) := by
  have hE1 := (energyInvariant cert) a hreal hsmall hT g t ht
  have hsqrt : Real.sqrt (criticalEnergy 1 N (g.coeff t)) ≤ ‖a‖ := by
    calc
      _ ≤ Real.sqrt (‖a‖ ^ 2) := Real.sqrt_le_sqrt hE1
      _ = _ := Real.sqrt_sq (norm_nonneg a)
  have hE2 : criticalEnergy 2 N (g.coeff t) ≤
      ‖a‖ * Real.sqrt (criticalEnergy 3 N (g.coeff t)) :=
    (criticalEnergy_interpolation_sqrt N (g.coeff t)).trans
      (mul_le_mul_of_nonneg_right hsqrt (Real.sqrt_nonneg _))
  rw [g.criticalRhs_eq_finiteSobolev (-1) t ht.1]
  calc
    _ ≤ ν * Real.sqrt (criticalEnergy 3 N (g.coeff t)) +
        criticalTransportConstant * criticalEnergy 2 N (g.coeff t) :=
      criticalFiniteSobolev_rhs_neg_one_bound ν hν N (g.coeff t)
        (g.mode_support t ht.1) (g.real_symmetry t ht.1)
    _ ≤ ν * Real.sqrt (criticalEnergy 3 N (g.coeff t)) +
        criticalTransportConstant * (‖a‖ * Real.sqrt (criticalEnergy 3 N (g.coeff t))) :=
      add_le_add (le_refl _)
        (mul_le_mul_of_nonneg_left hE2 criticalTransportConstant_pos.le)
    _ = _ := by ring

theorem timeDerivativeSquare (cert : NonlinearCertificate)
    {ν T : ℝ} {N : ℕ} (hν : 0 ≤ ν) (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hsmall : cert.constant * ‖a‖ < ν) (hT : 0 ≤ T)
    (g : GalerkinSolution ν (finiteSynthesis N (criticalCoeff 1 a)) N)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖g.criticalRhs (-1) t‖ ^ 2 ≤
      (ν + criticalTransportConstant * ‖a‖) ^ 2 * criticalEnergy 3 N (g.coeff t) := by
  have h := pow_le_pow_left₀ (norm_nonneg (g.criticalRhs (-1) t))
    ((timeDerivativePointwise cert) hν a hreal hsmall hT g ht) 2
  simpa only [mul_pow, Real.sq_sqrt (criticalEnergy_nonneg 3 N (g.coeff t))] using h

theorem timeDerivativeBudget (cert : NonlinearCertificate)
    {ν T : ℝ} {N : ℕ} (hν : 0 ≤ ν) (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hsmall : cert.constant * ‖a‖ < ν) (hT : 0 ≤ T)
    (g : GalerkinSolution ν (finiteSynthesis N (criticalCoeff 1 a)) N) :
    (∫ t in (0 : ℝ)..T, ‖g.criticalRhs (-1) t‖ ^ 2) ≤
      (ν + criticalTransportConstant * ‖a‖) ^ 2 * ‖a‖ ^ 2 /
        (2 * (ν - cert.constant * ‖a‖)) := by
  have hδ : 0 < 2 * (ν - cert.constant * ‖a‖) :=
    mul_pos (by norm_num) (sub_pos.mpr hsmall)
  have hE3 : (∫ t in (0 : ℝ)..T, criticalEnergy 3 N (g.coeff t)) ≤
      ‖a‖ ^ 2 / (2 * (ν - cert.constant * ‖a‖)) := by
    have h := (dissipationBudget cert) a hreal hsmall hT g T ⟨hT, le_rfl⟩
    apply (le_div_iff₀ hδ).2
    have hnonneg := criticalEnergy_nonneg 1 N (g.coeff T)
    nlinarith
  have hRint : IntervalIntegrable (fun t => ‖g.criticalRhs (-1) t‖ ^ 2) volume 0 T :=
    (((g.criticalRhs_continuousOn (-1)).mono
      (fun _ (ht : _ ∈ Icc (0 : ℝ) T) => ht.1)).norm.pow 2).intervalIntegrable_of_Icc hT
  have hEint : IntervalIntegrable (fun t => criticalEnergy 3 N (g.coeff t)) volume 0 T :=
    ((g.criticalEnergy_continuousOn 3).mono (fun t ht => ht.1)).intervalIntegrable_of_Icc hT
  calc
    _ ≤ ∫ t in (0 : ℝ)..T,
        (ν + criticalTransportConstant * ‖a‖) ^ 2 * criticalEnergy 3 N (g.coeff t) := by
      apply intervalIntegral.integral_mono_on hT hRint (hEint.const_mul _)
      intro t ht
      exact (timeDerivativeSquare cert) hν a hreal hsmall hT g ht
    _ = (ν + criticalTransportConstant * ‖a‖) ^ 2 *
        (∫ t in (0 : ℝ)..T, criticalEnergy 3 N (g.coeff t)) :=
      intervalIntegral.integral_const_mul _ _
    _ ≤ (ν + criticalTransportConstant * ‖a‖) ^ 2 *
        (‖a‖ ^ 2 / (2 * (ν - cert.constant * ‖a‖))) :=
      mul_le_mul_of_nonneg_left hE3 (sq_nonneg _)
    _ = _ := by ring

end
end SingularClosure.H12Frontier.Replay
