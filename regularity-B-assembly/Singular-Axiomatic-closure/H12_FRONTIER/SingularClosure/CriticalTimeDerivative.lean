import SingularClosure.CriticalNegativeTransport
import SingularClosure.CriticalGalerkinTrajectory
import SingularClosure.SmallDataAX6Closure

/-! Actual negative-half-order Galerkin time derivatives and their uniform
integrated bound. Both viscosity and nonlinear transport are literal terms
of the original coefficient ODE. -/

set_option autoImplicit false
set_option Elab.async true

noncomputable section

open Set MeasureTheory
open scoped Interval ENNReal

namespace SingularClosure

def criticalTransportConstant : ℝ := FINITE_CRITICAL_NEGATIVE_TRANSPORT_BOUND.choose

theorem criticalTransportConstant_pos : 0 < criticalTransportConstant :=
  FINITE_CRITICAL_NEGATIVE_TRANSPORT_BOUND.choose_spec.1

theorem criticalTransportConstant_bound (N : ℕ) (c : FourierCoeff)
    (hsupp : ∀ k : Frequency, k ∉ cutoffModes N → ∀ i : Fin 3, c k i = 0)
    (hreal : SpectralReality c) :
    ‖criticalFiniteSobolev (-1) N (criticalProjectedTransport N c)‖ ≤
      criticalTransportConstant * criticalEnergy 2 N c :=
  FINITE_CRITICAL_NEGATIVE_TRANSPORT_BOUND.choose_spec.2 N c hsupp hreal

theorem criticalFiniteSobolev_rhs_decomposition
    (q : ℤ) (ν : ℝ) (N : ℕ) (c : FourierCoeff) :
    criticalFiniteSobolev q N (galerkinRhs ν N c) =
      (ν : ℂ) • criticalFiniteSobolev q N (laplacianCoefficient c) +
        (-1 : ℂ) • criticalFiniteSobolev q N (criticalProjectedTransport N c) := by
  apply criticalCoeff_injective q
  rw [criticalCoeff_add, criticalCoeff_smul, criticalCoeff_smul,
    criticalFiniteSobolev_coeff, criticalFiniteSobolev_coeff, criticalFiniteSobolev_coeff]
  funext k i
  by_cases hk : k ∈ cutoffModes N
  · simp only [cutoffCoeff, if_pos hk, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      galerkinRhs, laplacianCoefficient, laplacianFrequency, criticalProjectedTransport]
    push_cast
    ring
  · simp [cutoffCoeff, hk]

theorem criticalFiniteSobolev_laplacian_neg_one_norm (N : ℕ) (c : FourierCoeff) :
    ‖criticalFiniteSobolev (-1) N (laplacianCoefficient c)‖ =
      Real.sqrt (criticalEnergy 3 N c) := by
  rw [← criticalNegativeEnergy_laplacianCoefficient N c,
    ← criticalFiniteSobolev_neg_one_norm_sq N (laplacianCoefficient c),
    Real.sqrt_sq (norm_nonneg _)]

/-- Pointwise bound for the literal finite Fourier right-hand side. -/
theorem criticalFiniteSobolev_rhs_neg_one_bound
    (ν : ℝ) (hν : 0 ≤ ν) (N : ℕ) (c : FourierCoeff)
    (hsupp : ∀ k : Frequency, k ∉ cutoffModes N → ∀ i : Fin 3, c k i = 0)
    (hreal : SpectralReality c) :
    ‖criticalFiniteSobolev (-1) N (galerkinRhs ν N c)‖ ≤
      ν * Real.sqrt (criticalEnergy 3 N c) +
        criticalTransportConstant * criticalEnergy 2 N c := by
  rw [criticalFiniteSobolev_rhs_decomposition]
  calc
    _ ≤ ‖(ν : ℂ) • criticalFiniteSobolev (-1) N (laplacianCoefficient c)‖ +
        ‖(-1 : ℂ) • criticalFiniteSobolev (-1) N (criticalProjectedTransport N c)‖ :=
      norm_add_le _ _
    _ = ν * Real.sqrt (criticalEnergy 3 N c) +
        ‖criticalFiniteSobolev (-1) N (criticalProjectedTransport N c)‖ := by
      rw [norm_smul, norm_smul, norm_neg, norm_one, one_mul,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hν,
        criticalFiniteSobolev_laplacian_neg_one_norm]
    _ ≤ _ := add_le_add (le_refl _) (criticalTransportConstant_bound N c hsupp hreal)

theorem criticalGalerkin_timeDerivative_pointwise_bound
    {ν T : ℝ} {N : ℕ} (hν : 0 ≤ ν) (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hsmall : criticalNonlinearConstant * ‖a‖ < ν) (hT : 0 ≤ T)
    (g : GalerkinSolution ν (finiteSynthesis N (criticalCoeff 1 a)) N)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖g.criticalRhs (-1) t‖ ≤
      (ν + criticalTransportConstant * ‖a‖) * Real.sqrt (criticalEnergy 3 N (g.coeff t)) := by
  have hE1 := criticalGalerkin_energy_invariant a hreal hsmall hT g t ht
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

theorem criticalGalerkin_timeDerivative_square_bound
    {ν T : ℝ} {N : ℕ} (hν : 0 ≤ ν) (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hsmall : criticalNonlinearConstant * ‖a‖ < ν) (hT : 0 ≤ T)
    (g : GalerkinSolution ν (finiteSynthesis N (criticalCoeff 1 a)) N)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖g.criticalRhs (-1) t‖ ^ 2 ≤
      (ν + criticalTransportConstant * ‖a‖) ^ 2 * criticalEnergy 3 N (g.coeff t) := by
  have h := pow_le_pow_left₀ (norm_nonneg (g.criticalRhs (-1) t))
    (criticalGalerkin_timeDerivative_pointwise_bound hν a hreal hsmall hT g ht) 2
  simpa only [mul_pow, Real.sq_sqrt (criticalEnergy_nonneg 3 N (g.coeff t))] using h

/-- A finite uniform bound for the actual H^(-1/2) time derivative. -/
theorem CRITICAL_GALERKIN_TIME_DERIVATIVE_BUDGET
    {ν T : ℝ} {N : ℕ} (hν : 0 ≤ ν) (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hsmall : criticalNonlinearConstant * ‖a‖ < ν) (hT : 0 ≤ T)
    (g : GalerkinSolution ν (finiteSynthesis N (criticalCoeff 1 a)) N) :
    (∫ t in (0 : ℝ)..T, ‖g.criticalRhs (-1) t‖ ^ 2) ≤
      (ν + criticalTransportConstant * ‖a‖) ^ 2 * ‖a‖ ^ 2 /
        (2 * (ν - criticalNonlinearConstant * ‖a‖)) := by
  have hδ : 0 < 2 * (ν - criticalNonlinearConstant * ‖a‖) :=
    mul_pos (by norm_num) (sub_pos.mpr hsmall)
  have hE3 : (∫ t in (0 : ℝ)..T, criticalEnergy 3 N (g.coeff t)) ≤
      ‖a‖ ^ 2 / (2 * (ν - criticalNonlinearConstant * ‖a‖)) := by
    have h := criticalGalerkin_dissipation_budget a hreal hsmall hT g T ⟨hT, le_rfl⟩
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
      exact criticalGalerkin_timeDerivative_square_bound hν a hreal hsmall hT g ht
    _ = (ν + criticalTransportConstant * ‖a‖) ^ 2 *
        (∫ t in (0 : ℝ)..T, criticalEnergy 3 N (g.coeff t)) :=
      intervalIntegral.integral_const_mul _ _
    _ ≤ (ν + criticalTransportConstant * ‖a‖) ^ 2 *
        (‖a‖ ^ 2 / (2 * (ν - criticalNonlinearConstant * ‖a‖))) :=
      mul_le_mul_of_nonneg_left hE3 (sq_nonneg _)
    _ = _ := by ring

end SingularClosure
