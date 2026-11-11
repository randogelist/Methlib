import SingularClosure.CriticalTimeDerivative
import SingularClosure.CriticalLimitGlobal

/-! Concrete critical Galerkin bounds instantiate global coefficient and
Hilbert-space compactness without auxiliary analytic premises. -/

set_option autoImplicit false
set_option Elab.async true

noncomputable section

open Set MeasureTheory Filter
open scoped Interval ENNReal Topology

namespace SingularClosure

theorem GalerkinSolution.criticalState_norm_sq_nat
    {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N)
    (q : ℕ) (t : ℝ) :
    ‖g.criticalState (q : ℤ) t‖ ^ 2 = criticalEnergy q N (g.coeff t) := by
  rw [GalerkinSolution.criticalState, criticalFiniteSobolev_norm_sq]
  simp only [criticalEnergy, zpow_natCast]

theorem criticalGalerkin_state_norm_le
    {ν : ℝ} {N : ℕ} (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hsmall : criticalNonlinearConstant * ‖a‖ < ν)
    (g : GalerkinSolution ν (finiteSynthesis N (criticalCoeff 1 a)) N)
    {t : ℝ} (ht : 0 ≤ t) : ‖g.criticalState 1 t‖ ≤ ‖a‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg a)).mp
  rw [g.criticalState_norm_sq_nat 1 t]
  exact criticalGalerkin_energy_invariant a hreal hsmall ht g t ⟨ht, le_rfl⟩

def criticalDissipationBudget (ν : ℝ) (a : CriticalSobolev 1) : ℝ :=
  ‖a‖ ^ 2 / (2 * (ν - criticalNonlinearConstant * ‖a‖))

def criticalTimeDerivativeBudget (ν : ℝ) (a : CriticalSobolev 1) : ℝ :=
  (ν + criticalTransportConstant * ‖a‖) ^ 2 * ‖a‖ ^ 2 /
    (2 * (ν - criticalNonlinearConstant * ‖a‖))

theorem criticalDissipationBudget_nonneg
    {ν : ℝ} (a : CriticalSobolev 1)
    (hsmall : criticalNonlinearConstant * ‖a‖ < ν) :
    0 ≤ criticalDissipationBudget ν a :=
  div_nonneg (sq_nonneg _)
    (mul_nonneg (by norm_num) (sub_pos.mpr hsmall).le)

theorem criticalTimeDerivativeBudget_nonneg
    {ν : ℝ} (a : CriticalSobolev 1)
    (hsmall : criticalNonlinearConstant * ‖a‖ < ν) :
    0 ≤ criticalTimeDerivativeBudget ν a :=
  div_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    (mul_nonneg (by norm_num) (sub_pos.mpr hsmall).le)

theorem criticalGalerkin_state_three_integral_bound
    {ν T : ℝ} {N : ℕ} (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hsmall : criticalNonlinearConstant * ‖a‖ < ν) (hT : 0 ≤ T)
    (g : GalerkinSolution ν (finiteSynthesis N (criticalCoeff 1 a)) N) :
    (∫ t in (0 : ℝ)..T, ‖g.criticalState 3 t‖ ^ 2) ≤ criticalDissipationBudget ν a := by
  have h := criticalGalerkin_dissipation_budget a hreal hsmall hT g T ⟨hT, le_rfl⟩
  have hnonneg := criticalEnergy_nonneg 1 N (g.coeff T)
  simp_rw [g.criticalState_norm_sq_nat 3]
  apply (le_div_iff₀
    (mul_pos (by norm_num : (0 : ℝ) < 2) (sub_pos.mpr hsmall))).2
  nlinarith

/-- The literal cutoff family for a single rough critical datum. -/
def criticalDatumGalerkinFamily (ν : ℝ) (hν : 0 ≤ ν) (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hsol : SpectralSolenoidal (criticalCoeff 1 a)) (n : ℕ) :
    GalerkinSolution ν (finiteSynthesis (n + 1) (criticalCoeff 1 a)) (n + 1) :=
  criticalGalerkinSolution ν hν (criticalCoeff 1 a) hreal hsol (n + 1)

/-- Actual global subsequence extraction under smallness alone, with one
common strictly increasing subsequence for all finite time horizons. -/
theorem SMALL_DATA_GALERKIN_GLOBAL_COMPACTNESS
    (ν : ℝ) (hν : 0 ≤ ν) (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hsol : SpectralSolenoidal (criticalCoeff 1 a))
    (hsmall : criticalNonlinearConstant * ‖a‖ < ν) :
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
    ‖a‖ (criticalDissipationBudget ν a) (criticalTimeDerivativeBudget ν a)
    (norm_nonneg a) (criticalDissipationBudget_nonneg a hsmall)
    (criticalTimeDerivativeBudget_nonneg a hsmall)
  · intro n t ht
    exact criticalGalerkin_state_norm_le a hreal hsmall _ ht
  · intro n T hT
    exact criticalGalerkin_state_three_integral_bound a hreal hsmall hT _
  · intro n T hT
    exact CRITICAL_GALERKIN_TIME_DERIVATIVE_BUDGET hν a hreal hsmall hT _

end SingularClosure
