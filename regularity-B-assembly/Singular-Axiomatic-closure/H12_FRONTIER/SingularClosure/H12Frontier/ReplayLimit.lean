import SingularClosure.H12Frontier.ReplayCompactness
import SingularClosure.CriticalQuantitative

/-! Certificate-parametric replay. The registered fixed-coefficient milestone
is a separate specialization; this module does not assert that coefficient. -/
set_option autoImplicit false
set_option Elab.async true
open Set MeasureTheory Filter
open scoped BigOperators Topology Interval NNReal ENNReal
namespace SingularClosure.H12Frontier.Replay
noncomputable section

theorem limitQuartic (cert : NonlinearCertificate)
    (ν : ℝ) (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hsmall : cert.constant * ‖a‖ < ν)
    (φ : ℕ → ℕ)
    (g : ∀ n, GalerkinSolution ν
      (finiteSynthesis (φ n + 1) (criticalCoeff 1 a)) (φ n + 1))
    (u : ℝ → CriticalSobolev 1) (T : ℝ) (hT : 0 ≤ T)
    (hconv : TendstoUniformlyOn (fun n t => (g n).sobolevState 0 t)
      (fun t => criticalToTorusH0 1 (by norm_num) (u t)) atTop (Icc (0 : ℝ) T)) :
    ENNReal.ofReal (‖u T‖ ^ 4) +
      ENNReal.ofReal (4 * (ν - cert.constant * ‖a‖)) *
        (∫⁻ t in Icc (0 : ℝ) T,
          criticalExtendedSquare 2 (criticalCoeff 1 (u t)) ^ 2) ≤ ENNReal.ofReal (‖a‖ ^ 4) := by
  have hcoeff (q : ℤ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (k : Frequency) (i : Fin 3) :
      Tendsto (fun n => criticalCoeff q ((g n).criticalState q t) k i) atTop
        (𝓝 (criticalCoeff 1 (u t) k i)) := by
    simpa only [criticalToTorusH0_coeff] using
      criticalGalerkinLimit_criticalState_coeff_tendsto ν
        (fun n => finiteSynthesis (φ n + 1) (criticalCoeff 1 a)) φ g
        (fun t => criticalToTorusH0 1 (by norm_num) (u t)) T hconv q t ht k i
  have hbudget (n : ℕ) : ‖(g n).criticalState 1 T‖ ^ 4 +
      (4 * (ν - cert.constant * ‖a‖)) *
        (∫ t in (0 : ℝ)..T, ‖(g n).criticalState 2 t‖ ^ 4) ≤ ‖a‖ ^ 4 := by
    have h := (sharpSquareBudget cert) a hreal hsmall hT (g n)
    have hp : 0 < 4 * (ν - cert.constant * ‖a‖) :=
      mul_pos (by norm_num) (sub_pos.mpr hsmall)
    have hmul := (le_div_iff₀ hp).mp h
    have hnorm1 : ‖(g n).criticalState 1 T‖ ^ 2 =
        criticalEnergy 1 (φ n + 1) ((g n).coeff T) := by
      rw [GalerkinSolution.criticalState, criticalFiniteSobolev_norm_sq]
      simp only [criticalEnergy, zpow_one, pow_one]
    have hnorm2 (t : ℝ) : ‖(g n).criticalState 2 t‖ ^ 2 =
        criticalEnergy 2 (φ n + 1) ((g n).coeff t) := by
      rw [GalerkinSolution.criticalState, criticalFiniteSobolev_norm_sq]
      simp only [criticalEnergy, zpow_ofNat]
    have hfour1 : ‖(g n).criticalState 1 T‖ ^ 4 =
        criticalEnergy 1 (φ n + 1) ((g n).coeff T) ^ 2 := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hnorm1]
    have hfour2 (t : ℝ) : ‖(g n).criticalState 2 t‖ ^ 4 =
        criticalEnergy 2 (φ n + 1) ((g n).coeff t) ^ 2 := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hnorm2]
    simp_rw [hfour1, hfour2, criticalEnergy_two_eq_coefficientDissipation]
    nlinarith
  have h := critical_modal_quartic_budget 2 1 T
    (4 * (ν - cert.constant * ‖a‖)) (‖a‖ ^ 4) hT
    (mul_nonneg (by norm_num) (sub_pos.mpr hsmall).le)
    (fun n => (g n).criticalState 2) (fun n => (g n).criticalState 1 T)
    (fun t => criticalCoeff 1 (u t)) (criticalCoeff 1 (u T))
    (fun n => ((g n).criticalState_continuousOn 2).mono (fun t ht => ht.1))
    (hcoeff 2) (hcoeff 1 T ⟨hT, le_rfl⟩) hbudget
  rw [criticalExtendedSquare_eq_norm,
    ← ENNReal.ofReal_pow (sq_nonneg _) 2, ← pow_mul] at h
  exact h

theorem limitNegativeHalf (cert : NonlinearCertificate)
    (ν : ℝ) (hν : 0 ≤ ν) (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hsmall : cert.constant * ‖a‖ < ν)
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (g : ∀ n, GalerkinSolution ν
      (finiteSynthesis (φ n + 1) (criticalCoeff 1 a)) (φ n + 1))
    (u : ℝ → CriticalSobolev 1) (T : ℝ) (hT : 0 ≤ T)
    (hu : ContinuousOn (fun t => criticalToTorusH0 1 (by norm_num) (u t)) (Icc (0 : ℝ) T))
    (hconv : TendstoUniformlyOn (fun n t => (g n).sobolevState 0 t)
      (fun t => criticalToTorusH0 1 (by norm_num) (u t)) atTop (Icc (0 : ℝ) T)) :
    ∃ V : ℝ → CriticalSobolev (-1),
      MemLp V 2 (volume.restrict (Icc (0 : ℝ) T)) ∧
      (∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T),
        criticalCoeff (-1) (V t) = fullFourierRhs ν (criticalToTorusH0 1 (by norm_num) (u t))) ∧
      (∫ t in Icc (0 : ℝ) T, ‖V t‖ ^ 2) ≤ (derivativeConstant cert) ν a := by
  exact criticalGalerkinLimit_rhs_memLp ν
    (fun n => finiteSynthesis (φ n + 1) (criticalCoeff 1 a)) φ hφ g
    (fun t => criticalToTorusH0 1 (by norm_num) (u t)) (-1) T
    ((derivativeConstant cert) ν a) hT ((derivativeConstant_nonneg cert) a hsmall)
    hu hconv (fun n => (timeDerivativeBudget cert) hν a hreal hsmall hT (g n))

end
end SingularClosure.H12Frontier.Replay
