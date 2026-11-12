import SingularClosure.H12Frontier.Contracts
import SingularClosure.SmallDataAX6Closure

/-! Certificate-parametric replay. The registered fixed-coefficient milestone
is a separate specialization; this module does not assert that coefficient. -/
set_option autoImplicit false
set_option Elab.async true
open Set MeasureTheory Filter
open scoped BigOperators Topology Interval NNReal ENNReal
namespace SingularClosure.H12Frontier.Replay
noncomputable section

theorem differentialInequality (cert : NonlinearCertificate)
    {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N)
    {t : ℝ} (ht : 0 ≤ t) :
    criticalEnergyRate ν 1 N (g.coeff t) +
      2 * (ν - cert.constant * Real.sqrt (criticalEnergy 1 N (g.coeff t))) *
        criticalEnergy 3 N (g.coeff t) ≤ 0 :=
  criticalEnergyRate_inequality_of_nonlinear_bound
    (cert.bound N (g.coeff t)
      (g.mode_support t ht) (g.real_symmetry t ht) (g.solenoidal t ht))

theorem energyInvariant (cert : NonlinearCertificate)
    {ν T : ℝ} {N : ℕ} (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hsmall : cert.constant * ‖a‖ < ν) (hT : 0 ≤ T)
    (g : GalerkinSolution ν (finiteSynthesis N (criticalCoeff 1 a)) N) :
    ∀ t ∈ Icc 0 T, criticalEnergy 1 N (g.coeff t) ≤ ‖a‖ ^ 2 :=
  CRITICAL_ENERGY_INVARIANT hT cert.positive.le (norm_nonneg a)
    hsmall ((g.criticalEnergy_continuousOn 1).mono (fun t ht => ht.1))
    (fun t _ => criticalEnergy_nonneg 3 N (g.coeff t))
    (criticalGalerkin_criticalEnergy_initial_le 1 a hreal g)
    (fun t ht => g.criticalEnergy_balance 1 ht.1)
    (fun t ht => (differentialInequality cert g) ht.1)

theorem dissipationBudget (cert : NonlinearCertificate)
    {ν T : ℝ} {N : ℕ} (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hsmall : cert.constant * ‖a‖ < ν) (hT : 0 ≤ T)
    (g : GalerkinSolution ν (finiteSynthesis N (criticalCoeff 1 a)) N) :
    ∀ t ∈ Icc 0 T,
      criticalEnergy 1 N (g.coeff t) + 2 * (ν - cert.constant * ‖a‖) *
        (∫ s in (0 : ℝ)..t, criticalEnergy 3 N (g.coeff s)) ≤ ‖a‖ ^ 2 :=
  CRITICAL_DISSIPATION_BUDGET hT cert.positive.le (norm_nonneg a)
    hsmall ((g.criticalEnergy_continuousOn 1).mono (fun t ht => ht.1))
    ((g.criticalEnergy_continuousOn 3).mono (fun t ht => ht.1))
    (fun t _ => criticalEnergy_nonneg 1 N (g.coeff t))
    (fun t _ => criticalEnergy_nonneg 3 N (g.coeff t))
    (criticalGalerkin_criticalEnergy_initial_le 1 a hreal g)
    (fun t ht => g.criticalEnergy_balance 1 ht.1)
    (fun t ht => (differentialInequality cert g) ht.1)

theorem sharpSquareBudget (cert : NonlinearCertificate)
    {ν T : ℝ} {N : ℕ} (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hsmall : cert.constant * ‖a‖ < ν) (hT : 0 ≤ T)
    (g : GalerkinSolution ν (finiteSynthesis N (criticalCoeff 1 a)) N) :
    (∫ t in (0 : ℝ)..T, coefficientDissipation N (g.coeff t) ^ 2) ≤
      (‖a‖ ^ 4 - criticalEnergy 1 N (g.coeff T) ^ 2) /
        (4 * (ν - cert.constant * ‖a‖)) := by
  have h := CRITICAL_SQUARE_BUDGET_DIV
    (A := fun t => criticalEnergy 1 N (g.coeff t))
    (B := fun t => criticalEnergy 3 N (g.coeff t))
    (X := fun t => criticalEnergy 2 N (g.coeff t))
    (d := fun t => criticalEnergyRate ν 1 N (g.coeff t))
    hT cert.positive.le (norm_nonneg a) hsmall
    ((g.criticalEnergy_continuousOn 1).mono (fun t ht => ht.1))
    ((g.criticalEnergy_continuousOn 2).mono (fun t ht => ht.1))
    (fun t _ => criticalEnergy_nonneg 1 N (g.coeff t))
    (fun t _ => criticalEnergy_nonneg 3 N (g.coeff t))
    (criticalGalerkin_criticalEnergy_initial_le 1 a hreal g)
    (fun t ht => g.criticalEnergy_balance 1 ht.1)
    (fun t ht => (differentialInequality cert g) ht.1)
    (fun t _ => criticalEnergy_interpolation N (g.coeff t))
  simpa only [criticalEnergy_two_eq_coefficientDissipation] using h

theorem sixChannelBudget (cert : NonlinearCertificate)
    {ν T : ℝ} {N : ℕ} (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hsmall : cert.constant * ‖a‖ < ν) (hT : 0 ≤ T)
    (g : GalerkinSolution ν (finiteSynthesis N (criticalCoeff 1 a)) N) :
    budget6 N g.coeff T ≤
      ENNReal.ofReal (‖a‖ ^ 4 / (4 * (ν - cert.constant * ‖a‖))) :=
  g.critical_budget6_of_differential_inequality hT cert.positive.le
    (norm_nonneg a) hsmall (criticalGalerkin_criticalEnergy_initial_le 1 a hreal g)
    (fun t ht => (differentialInequality cert g) ht.1)

theorem datumAX6 (cert : NonlinearCertificate)
    (ν : ℝ) (_hν : 0 < ν) (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (_hsol : SpectralSolenoidal (criticalCoeff 1 a))
    (_hzero : SpectralMeanZero (criticalCoeff 1 a))
    (hsmall : cert.constant * ‖a‖ < ν) :
    CriticalDatumAX6 ν a := by
  intro T hT
  let M : ℝ := ‖a‖ ^ 4 / (4 * (ν - cert.constant * ‖a‖))
  have hM : 0 ≤ M :=
    div_nonneg (pow_nonneg (norm_nonneg a) 4)
      (mul_nonneg (by norm_num) (sub_pos.mpr hsmall).le)
  refine ⟨Real.toNNReal M, ?_⟩
  intro N _ g
  change budget6 N g.coeff T ≤ ENNReal.ofReal M
  exact (sixChannelBudget cert) a hreal hsmall hT.le g

end
end SingularClosure.H12Frontier.Replay
