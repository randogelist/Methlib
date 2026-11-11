import SingularClosure.CriticalQuantitative
import SingularClosure.CriticalPositiveFlow
import SingularClosure.CriticalSmoothParseval

/-! Literal physical time derivatives and quantitative critical representatives. -/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory Filter
open scoped Topology Interval ENNReal

namespace SingularClosure
noncomputable section

theorem CriticalPositiveSobolevFlow.timeDerivative_fourierCoeff
    {ν : ℝ} (L : CriticalPositiveSobolevFlow ν) (t : ℝ) (ht : 0 < t) :
    datumFourierCoeff (timeDerivative L.velocity t) = fullFourierRhs ν (L.state 0 t) := by
  rw [L.velocity_timeDerivative t ht]
  apply datumFourierCoeff_smoothFourierSynthesis
  · intro i
    apply ALL_SOBOLEV_IMP_RAPID_SCALAR _ _ i
    intro s
    rw [← L.rhs_coeff s t ht]
    exact (fourierSobolevRhs ν s (L.state (s + 2) t)).property
  · exact fullFourierRhs_reality ν (L.state 0 t) (L.state_all_mem t ht)
      (L.reality t ht) (L.solenoidal t ht)

theorem critical_ae_positive_on_Icc (T : ℝ) :
    ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T), 0 < t := by
  rw [← MeasureTheory.restrict_Ioc_eq_restrict_Icc]
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact ht.1

/-- The representative is that of the actual physical time derivative,
identified by literal normalized-cube Fourier integration. -/
theorem critical_negative_representative_physical
    {ν : ℝ} (L : CriticalPositiveSobolevFlow ν)
    (u : ℝ → CriticalSobolev 1)
    (hL : ∀ t : ℝ, 0 < t → (L.state 0 t).val = criticalCoeff 1 (u t))
    (T : ℝ) (V : ℝ → CriticalSobolev (-1))
    (hV : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T),
      criticalCoeff (-1) (V t) = fullFourierRhs ν (criticalToTorusH0 1 (by norm_num) (u t))) :
    ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T),
      criticalCoeff (-1) (V t) = datumFourierCoeff (timeDerivative L.velocity t) := by
  filter_upwards [hV, critical_ae_positive_on_Icc T] with t hVt ht
  rw [L.timeDerivative_fourierCoeff t ht]
  have heq : L.state 0 t = criticalToTorusH0 1 (by norm_num) (u t) := by
    apply Subtype.ext
    rw [criticalToTorusH0_coeff]
    exact hL t ht
  rw [heq]
  exact hVt

theorem SMALL_DATA_LIMIT_PHYSICAL_NEGATIVE_HALF
    (ν : ℝ) (hν : 0 ≤ ν) (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hsmall : criticalNonlinearConstant * ‖a‖ < ν)
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
      (∫ t in Icc (0 : ℝ) T, ‖V t‖ ^ 2) ≤ criticalTimeDerivativeBudget ν a := by
  obtain ⟨V, hV, hVc, hVb⟩ := SMALL_DATA_LIMIT_NEGATIVE_HALF ν hν a hreal hsmall
    φ hφ g u T hT hu hconv
  exact ⟨V, hV, critical_negative_representative_physical L u hL T V hVc, hVb⟩

theorem criticalFrequencyWeight_le_torusSobolevWeight (k : Frequency) :
    criticalFrequencyWeight k ≤ torusSobolevWeight k := by
  by_cases hk : k = 0
  · subst k
    rw [criticalFrequencyWeight_zero]
    exact torusSobolevWeight_one_le 0
  · have hw := criticalFrequencyWeight_sq_of_ne_zero k hk
    have ht := torusSobolevWeight_sq k
    change criticalFrequencyWeight k ^ 2 =
      (2 * Real.pi) ^ 2 * (galerkinFreqSq k : ℝ) at hw
    apply (sq_le_sq₀ (criticalFrequencyWeight_pos k).le (torusSobolevWeight_pos k).le).mp
    linarith

theorem critical_order_two_mem_of_torus_one (c : FourierCoeff)
    (hc : Memℓp (sobolevWeightedCoeff 1 c) 2) :
    Memℓp (criticalWeightedCoeff 2 c) 2 := by
  apply hc.mono'
  intro ki
  have h := mul_le_mul_of_nonneg_right
    (criticalFrequencyWeight_le_torusSobolevWeight ki.1) (norm_nonneg (c ki.1 ki.2))
  simpa only [criticalWeightedCoeff_norm, zpow_ofNat, criticalHalfWeight_sq,
    sobolevWeightedCoeff, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (torusSobolevWeight_pos ki.1), pow_one] using h

theorem critical_smooth_extendedSquare_eq_dissipation
    (c : FourierCoeff) (hc : ∀ s : ℕ, Memℓp (sobolevWeightedCoeff s c) 2)
    (hreal : SpectralReality c) (hzero : SpectralMeanZero c) :
    criticalExtendedSquare 2 c = ENNReal.ofReal (physicalDissipation (smoothFourierSynthesis c)) := by
  let w : CriticalSobolev 2 :=
    criticalSobolevOfCoeff 2 c (critical_order_two_mem_of_torus_one c (hc 1))
  have hw : criticalCoeff 2 w = c := criticalSobolevOfCoeff_coeff _ _ _
  rw [critical_smoothFourierSynthesis_dissipation_eq_norm_sq c
    (ALL_SOBOLEV_IMP_RAPID_SCALAR c hc) hreal hzero w hw]
  simpa only [hw] using criticalExtendedSquare_eq_norm 2 w

/-- Literal physical fourth-gradient budget with the retained terminal
critical energy. The time integral is finite as part of the conclusion. -/
theorem SMALL_DATA_LIMIT_PHYSICAL_SHARP_QUARTIC
    (ν : ℝ) (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hsmall : criticalNonlinearConstant * ‖a‖ < ν)
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
        (‖a‖ ^ 4 - ‖u T‖ ^ 4) / (4 * (ν - criticalNonlinearConstant * ‖a‖)) := by
  let μ : Measure ℝ := volume.restrict (Icc (0 : ℝ) T)
  let δ : ℝ := 4 * (ν - criticalNonlinearConstant * ‖a‖)
  have hδ : 0 < δ := mul_pos (by norm_num) (sub_pos.mpr hsmall)
  have hD (t : ℝ) : 0 ≤ physicalDissipation (L.velocity t) :=
    integral_nonneg (gradientSquareDensity_nonneg (L.velocity t))
  have heq : (fun t => criticalExtendedSquare 2 (criticalCoeff 1 (u t)) ^ 2) =ᵐ[μ]
      (fun t => ENNReal.ofReal (physicalDissipation (L.velocity t) ^ 2)) := by
    filter_upwards [critical_ae_positive_on_Icc T] with t ht
    rw [← hL t ht, critical_smooth_extendedSquare_eq_dissipation _
      (L.state_all_mem t ht) (L.reality t ht) (L.mean_zero t ht)]
    exact (ENNReal.ofReal_pow (hD t) 2).symm
  have hsharp := SMALL_DATA_LIMIT_SHARP_QUARTIC ν a hreal hsmall φ g u T hT hconv
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
      simpa only [criticalToTorusH0_coeff] using
        (torusSobolevH0Coeff_continuous ki.1 ki.2).comp_continuousOn hu
    have hm := (hcoeff.const_mul ((criticalHalfWeight ki.1 : ℂ) ^ (2 : ℤ))).norm.pow 2
    exact (hm.aestronglyMeasurable_of_isCompact
      isCompact_Icc measurableSet_Icc).aemeasurable.ennreal_ofReal
  have hmeas : AEStronglyMeasurable (fun t => physicalDissipation (L.velocity t) ^ 2) μ := by
    apply (hE.pow 2).ennreal_toReal.aestronglyMeasurable.congr
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
end SingularClosure
