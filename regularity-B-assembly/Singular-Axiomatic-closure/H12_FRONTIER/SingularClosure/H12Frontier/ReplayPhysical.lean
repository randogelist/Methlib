import SingularClosure.H12Frontier.ReplayLimit
import SingularClosure.CriticalPhysicalQuantitative

/-! Certificate-parametric replay. The registered fixed-coefficient milestone
is a separate specialization; this module does not assert that coefficient. -/
set_option autoImplicit false
set_option Elab.async true
open Set MeasureTheory Filter
open scoped BigOperators Topology Interval NNReal ENNReal
namespace SingularClosure.H12Frontier.Replay
noncomputable section

theorem physicalNegativeHalf (cert : NonlinearCertificate)
    (ν : ℝ) (hν : 0 ≤ ν) (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hsmall : cert.constant * ‖a‖ < ν)
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (g : ∀ n, GalerkinSolution ν
      (finiteSynthesis (φ n + 1) (criticalCoeff 1 a)) (φ n + 1))
    (u : ℝ → CriticalSobolev 1) (L : CriticalPositiveSobolevFlow ν)
    (hL : ∀ t : ℝ, 0 < t → (L.state 0 t).val = criticalCoeff 1 (u t))
    (T : ℝ) (hT : 0 ≤ T)
    (hu : ContinuousOn (fun t => criticalToTorusH0 1 (by norm_num) (u t)) (Icc (0 : ℝ) T))
    (hconv : TendstoUniformlyOn (fun n t => (g n).sobolevState 0 t)
      (fun t => criticalToTorusH0 1 (by norm_num) (u t)) atTop (Icc (0 : ℝ) T)) :
    ∃ V : ℝ → CriticalSobolev (-1),
      MemLp V 2 (volume.restrict (Icc (0 : ℝ) T)) ∧
      (∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T),
        criticalCoeff (-1) (V t) = datumFourierCoeff (timeDerivative L.velocity t)) ∧
      (∫ t in Icc (0 : ℝ) T, ‖V t‖ ^ 2) ≤ (derivativeConstant cert) ν a := by
  obtain ⟨V, hV, hVc, hVb⟩ := (limitNegativeHalf cert) ν hν a hreal hsmall
    φ hφ g u T hT hu hconv
  exact ⟨V, hV, critical_negative_representative_physical L u hL T V hVc, hVb⟩

theorem physicalQuartic (cert : NonlinearCertificate)
    (ν : ℝ) (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hsmall : cert.constant * ‖a‖ < ν)
    (φ : ℕ → ℕ)
    (g : ∀ n, GalerkinSolution ν
      (finiteSynthesis (φ n + 1) (criticalCoeff 1 a)) (φ n + 1))
    (u : ℝ → CriticalSobolev 1) (L : CriticalPositiveSobolevFlow ν)
    (hL : ∀ t : ℝ, 0 < t → (L.state 0 t).val = criticalCoeff 1 (u t))
    (T : ℝ) (hT : 0 ≤ T)
    (hu : ContinuousOn (fun t => criticalToTorusH0 1 (by norm_num) (u t)) (Icc (0 : ℝ) T))
    (hconv : TendstoUniformlyOn (fun n t => (g n).sobolevState 0 t)
      (fun t => criticalToTorusH0 1 (by norm_num) (u t)) atTop (Icc (0 : ℝ) T)) :
    IntegrableOn (fun t => physicalDissipation (L.velocity t) ^ 2) (Icc (0 : ℝ) T) volume ∧
      (∫ t in (0 : ℝ)..T, physicalDissipation (L.velocity t) ^ 2) ≤
        (‖a‖ ^ 4 - ‖u T‖ ^ 4) / (4 * (ν - cert.constant * ‖a‖)) := by
  let μ : Measure ℝ := volume.restrict (Icc (0 : ℝ) T)
  let δ : ℝ := 4 * (ν - cert.constant * ‖a‖)
  have hδ : 0 < δ := mul_pos (by norm_num) (sub_pos.mpr hsmall)
  have hD (t : ℝ) : 0 ≤ physicalDissipation (L.velocity t) :=
    integral_nonneg (gradientSquareDensity_nonneg (L.velocity t))
  have heq : (fun t => criticalExtendedSquare 2 (criticalCoeff 1 (u t)) ^ 2) =ᵐ[μ]
      (fun t => ENNReal.ofReal (physicalDissipation (L.velocity t) ^ 2)) := by
    filter_upwards [critical_ae_positive_on_Icc T] with t ht
    rw [← hL t ht, critical_smooth_extendedSquare_eq_dissipation _
      (L.state_all_mem t ht) (L.reality t ht) (L.mean_zero t ht)]
    exact (ENNReal.ofReal_pow (hD t) 2).symm
  have hsharp := (limitQuartic cert) ν a hreal hsmall φ g u T hT hconv
  rw [lintegral_congr_ae heq] at hsharp
  have hlin : (∫⁻ t, ENNReal.ofReal (physicalDissipation (L.velocity t) ^ 2) ∂μ) < ∞ := by
    have hp : ENNReal.ofReal δ *
        (∫⁻ t, ENNReal.ofReal (physicalDissipation (L.velocity t) ^ 2) ∂μ) < ∞ :=
      (le_add_left le_rfl).trans_lt (hsharp.trans_lt ENNReal.ofReal_lt_top)
    exact ENNReal.lt_top_of_mul_ne_top_right hp.ne (ne_of_gt (ENNReal.ofReal_pos.mpr hδ))
  have hE : AEMeasurable (fun t => criticalExtendedSquare 2 (criticalCoeff 1 (u t))) μ := by
    apply AEMeasurable.tsum
    intro ki
    have hcoeff : ContinuousOn (fun t => criticalCoeff 1 (u t) ki.1 ki.2) (Icc (0 : ℝ) T) := by
      simpa only [Function.comp_def, criticalToTorusH0_coeff] using
        (torusSobolevH0Coeff_continuous ki.1 ki.2).comp_continuousOn hu
    have hm := (hcoeff.const_mul ((criticalHalfWeight ki.1 : ℂ) ^ (2 : ℤ))).norm.pow 2
    exact (hm.aestronglyMeasurable_of_isCompact
      isCompact_Icc measurableSet_Icc).aemeasurable.ennreal_ofReal
  have hmeas : AEStronglyMeasurable (fun t => physicalDissipation (L.velocity t) ^ 2) μ := by
    apply (hE.pow_const (2 : ℕ)).ennreal_toReal.aestronglyMeasurable.congr
    filter_upwards [heq] with t ht
    rw [ht, ENNReal.toReal_ofReal (sq_nonneg _)]
  have hi : Integrable (fun t => physicalDissipation (L.velocity t) ^ 2) μ := by
    refine ⟨hmeas, ?_⟩
    change (∫⁻ t, ‖physicalDissipation (L.velocity t) ^ 2‖ₑ ∂μ) < ∞
    simpa only [Real.enorm_eq_ofReal (sq_nonneg _)] using hlin
  have hI : 0 ≤ ∫ t, physicalDissipation (L.velocity t) ^ 2 ∂μ :=
    integral_nonneg (fun t => sq_nonneg _)
  have hInt := ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall (fun t => sq_nonneg (physicalDissipation (L.velocity t))))
  rw [← hInt, ← ENNReal.ofReal_mul hδ.le,
    ← ENNReal.ofReal_add (pow_nonneg (norm_nonneg _) 4) (mul_nonneg hδ.le hI)] at hsharp
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hsharp
  rw [ENNReal.toReal_ofReal (add_nonneg (pow_nonneg (norm_nonneg _) 4) (mul_nonneg hδ.le hI)),
    ENNReal.toReal_ofReal (pow_nonneg (norm_nonneg _) 4)] at hr
  refine ⟨hi, ?_⟩
  rw [intervalIntegral.integral_of_le hT, ← integral_Icc_eq_integral_Ioc]
  apply (le_div_iff₀ hδ).2
  linarith

end
end SingularClosure.H12Frontier.Replay
