import SingularClosure.CriticalQuantitative

/-! The actual limiting H3/2 dissipation retains its terminal H1/2 energy. -/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory Filter
open scoped Topology Interval ENNReal

namespace SingularClosure
noncomputable section

theorem critical_modal_square_budget
    (q r : ℤ) (T δ A : ℝ) (hT : 0 ≤ T) (hδ : 0 ≤ δ)
    (F : ℕ → ℝ → CriticalSobolev q) (G : ℕ → CriticalSobolev r)
    (c : ℝ → FourierCoeff) (d : FourierCoeff)
    (hF : ∀ n, ContinuousOn (F n) (Icc (0 : ℝ) T))
    (hcoeff : ∀ t ∈ Icc (0 : ℝ) T, ∀ k i,
      Tendsto (fun n => criticalCoeff q (F n t) k i) atTop (𝓝 (c t k i)))
    (hterminal : ∀ k i,
      Tendsto (fun n => criticalCoeff r (G n) k i) atTop (𝓝 (d k i)))
    (hbudget : ∀ n, ‖G n‖ ^ 2 + δ * (∫ t in (0 : ℝ)..T, ‖F n t‖ ^ 2) ≤ A) :
    criticalExtendedSquare r d + ENNReal.ofReal δ *
      (∫⁻ t in Icc (0 : ℝ) T, criticalExtendedSquare q (c t)) ≤ ENNReal.ofReal A := by
  let μ : Measure ℝ := volume.restrict (Icc (0 : ℝ) T)
  let J : ℕ → ℝ≥0∞ := fun n => ∫⁻ t, ENNReal.ofReal (‖F n t‖ ^ 2) ∂μ
  have hterm := criticalExtendedSquare_le_liminf r G d hterminal
  have hint : (∫⁻ t, criticalExtendedSquare q (c t) ∂μ) ≤ atTop.liminf J := by
    calc
      _ ≤ ∫⁻ t, atTop.liminf (fun n => ENNReal.ofReal (‖F n t‖ ^ 2)) ∂μ := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
        exact criticalExtendedSquare_le_liminf q (fun n => F n t) (c t) (hcoeff t ht)
      _ ≤ atTop.liminf J := lintegral_liminf_le' (fun n =>
        (((hF n).norm.pow 2).aestronglyMeasurable_of_isCompact
          isCompact_Icc measurableSet_Icc).aemeasurable.ennreal_ofReal)
  have hmul : ENNReal.ofReal δ * atTop.liminf J ≤
      atTop.liminf (fun n => ENNReal.ofReal δ * J n) := by
    simpa only [Filter.liminf_const, Pi.mul_apply] using
      (ENNReal.le_liminf_mul (u := fun _ : ℕ => ENNReal.ofReal δ) (v := J) (f := atTop))
  have htotal (n : ℕ) : ENNReal.ofReal (‖G n‖ ^ 2) + ENNReal.ofReal δ * J n ≤
      ENNReal.ofReal A := by
    have hi : Integrable (fun t => ‖F n t‖ ^ 2) μ :=
      ((hF n).norm.pow 2).integrableOn_compact isCompact_Icc
    have heq := ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall (fun t => sq_nonneg (‖F n t‖)))
    have hI : 0 ≤ ∫ t, ‖F n t‖ ^ 2 ∂μ := integral_nonneg (fun t => sq_nonneg _)
    change ENNReal.ofReal (‖G n‖ ^ 2) + ENNReal.ofReal δ *
      (∫⁻ t, ENNReal.ofReal (‖F n t‖ ^ 2) ∂μ) ≤ _
    rw [← heq, ← ENNReal.ofReal_mul hδ,
      ← ENNReal.ofReal_add (sq_nonneg _) (mul_nonneg hδ hI)]
    apply ENNReal.ofReal_le_ofReal
    have h := hbudget n
    rw [intervalIntegral.integral_of_le hT, ← integral_Icc_eq_integral_Ioc] at h
    exact h
  calc
    _ ≤ atTop.liminf (fun n => ENNReal.ofReal (‖G n‖ ^ 2)) +
        ENNReal.ofReal δ * atTop.liminf J := by gcongr
    _ ≤ atTop.liminf (fun n => ENNReal.ofReal (‖G n‖ ^ 2)) +
        atTop.liminf (fun n => ENNReal.ofReal δ * J n) := add_le_add le_rfl hmul
    _ ≤ atTop.liminf (fun n => ENNReal.ofReal (‖G n‖ ^ 2) + ENNReal.ofReal δ * J n) :=
      critical_ennreal_liminf_add_le _ _
    _ ≤ ENNReal.ofReal A :=
      liminf_le_of_frequently_le' (Filter.Frequently.of_forall htotal)

theorem SMALL_DATA_LIMIT_TERMINAL_DISSIPATION
    (ν : ℝ) (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hsmall : criticalNonlinearConstant * ‖a‖ < ν)
    (φ : ℕ → ℕ)
    (g : ∀ n, GalerkinSolution ν
      (finiteSynthesis (φ n + 1) (criticalCoeff 1 a)) (φ n + 1))
    (u : ℝ → CriticalSobolev 1) (T : ℝ) (hT : 0 ≤ T)
    (hu : ContinuousOn (fun t => criticalToTorusH0 1 (by norm_num) (u t)) (Icc (0 : ℝ) T))
    (hconv : TendstoUniformlyOn (fun n t => (g n).sobolevState 0 t)
      (fun t => criticalToTorusH0 1 (by norm_num) (u t)) atTop (Icc (0 : ℝ) T)) :
    ∃ W : ℝ → CriticalSobolev 3,
      MemLp W 2 (volume.restrict (Icc (0 : ℝ) T)) ∧
      (∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T),
        criticalCoeff 3 (W t) = criticalCoeff 1 (u t)) ∧
      ‖u T‖ ^ 2 + 2 * (ν - criticalNonlinearConstant * ‖a‖) *
        (∫ t in Icc (0 : ℝ) T, ‖W t‖ ^ 2) ≤ ‖a‖ ^ 2 := by
  have hδ : 0 ≤ 2 * (ν - criticalNonlinearConstant * ‖a‖) :=
    mul_nonneg (by norm_num) (sub_pos.mpr hsmall).le
  have hcoeff (q : ℤ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (k : Frequency) (i : Fin 3) :
      Tendsto (fun n => criticalCoeff q ((g n).criticalState q t) k i) atTop
        (𝓝 (criticalCoeff 1 (u t) k i)) := by
    simpa only [criticalToTorusH0_coeff] using
      criticalGalerkinLimit_criticalState_coeff_tendsto ν
        (fun n => finiteSynthesis (φ n + 1) (criticalCoeff 1 a)) φ g
        (fun t => criticalToTorusH0 1 (by norm_num) (u t)) T hconv q t ht k i
  have hbudget (n : ℕ) : ‖(g n).criticalState 1 T‖ ^ 2 +
      (2 * (ν - criticalNonlinearConstant * ‖a‖)) *
        (∫ t in (0 : ℝ)..T, ‖(g n).criticalState 3 t‖ ^ 2) ≤ ‖a‖ ^ 2 := by
    have h1 : ‖(g n).criticalState 1 T‖ ^ 2 =
        criticalEnergy 1 (φ n + 1) ((g n).coeff T) := by
      rw [GalerkinSolution.criticalState, criticalFiniteSobolev_norm_sq]
      simp only [criticalEnergy, zpow_one, pow_one]
    have h3 (t : ℝ) : ‖(g n).criticalState 3 t‖ ^ 2 =
        criticalEnergy 3 (φ n + 1) ((g n).coeff t) := by
      simpa only [Nat.cast_ofNat] using (g n).criticalState_norm_sq_nat 3 t
    simp_rw [h1, h3]
    exact criticalGalerkin_dissipation_budget a hreal hsmall hT (g n) T ⟨hT, le_rfl⟩
  have h := critical_modal_square_budget 3 1 T
    (2 * (ν - criticalNonlinearConstant * ‖a‖)) (‖a‖ ^ 2) hT hδ
    (fun n => (g n).criticalState 3) (fun n => (g n).criticalState 1 T)
    (fun t => criticalCoeff 1 (u t)) (criticalCoeff 1 (u T))
    (fun n => ((g n).criticalState_continuousOn 3).mono (fun t ht => ht.1))
    (hcoeff 3) (hcoeff 1 T ⟨hT, le_rfl⟩) hbudget
  obtain ⟨W, hW, hWc, _hWb⟩ := criticalGalerkinLimit_state_memLp ν
    (fun n => finiteSynthesis (φ n + 1) (criticalCoeff 1 a)) φ g
    (fun t => criticalToTorusH0 1 (by norm_num) (u t)) 3 T
    (criticalDissipationBudget ν a) hT (criticalDissipationBudget_nonneg a hsmall) hu hconv
    (fun n => criticalGalerkin_state_three_integral_bound a hreal hsmall hT (g n))
  have hWc' : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T),
      criticalCoeff 3 (W t) = criticalCoeff 1 (u t) := by
    simpa only [criticalToTorusH0_coeff] using hWc
  have heq : (fun t => criticalExtendedSquare 3 (criticalCoeff 1 (u t))) =ᵐ[
      volume.restrict (Icc (0 : ℝ) T)] (fun t => ENNReal.ofReal (‖W t‖ ^ 2)) := by
    filter_upwards [hWc'] with t ht
    rw [← ht, criticalExtendedSquare_eq_norm]
  have hi := (memLp_two_iff_integrable_sq_norm hW.aestronglyMeasurable).mp hW
  have hI : 0 ≤ ∫ t in Icc (0 : ℝ) T, ‖W t‖ ^ 2 :=
    integral_nonneg (fun t => sq_nonneg _)
  have hInt := ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall (fun t => sq_nonneg (‖W t‖)))
  rw [criticalExtendedSquare_eq_norm, lintegral_congr_ae heq, ← hInt,
    ← ENNReal.ofReal_mul hδ, ← ENNReal.ofReal_add (sq_nonneg _) (mul_nonneg hδ hI)] at h
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  rw [ENNReal.toReal_ofReal (add_nonneg (sq_nonneg _) (mul_nonneg hδ hI)),
    ENNReal.toReal_ofReal (sq_nonneg _)] at hr
  exact ⟨W, hW, hWc', hr⟩

end
end SingularClosure
