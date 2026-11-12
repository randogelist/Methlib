import QuasiFeffermanB.EnergyGlobalPhysical
import SingularClosure.CriticalLimitFatou

/-! Passage of the Galerkin interval energy inequality to the actual modal
limit. The initial time is any time at which the approximating energies
converge; no strong convergence at every endpoint is assumed. -/
set_option autoImplicit false
set_option Elab.async true
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal Interval
namespace QuasiFeffermanB
open SingularClosure
noncomputable section

theorem energy_modal_eventually_lower
    (q : ℤ) (F : ℕ → CriticalSobolev q) (v : CriticalSobolev q)
    (hc : ∀ k i, Tendsto (fun n => criticalCoeff q (F n) k i)
      atTop (𝓝 (criticalCoeff q v k i)))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, ‖v‖ ^ 2 - ε ≤ ‖F n‖ ^ 2 := by
  by_cases hsmall : ‖v‖ ^ 2 ≤ ε
  · exact Eventually.of_forall (fun n => by nlinarith [sq_nonneg ‖F n‖])
  have hpos : 0 < ‖v‖ ^ 2 := by nlinarith
  have hlow := criticalExtendedSquare_le_liminf q F (criticalCoeff q v) hc
  rw [criticalExtendedSquare_eq_norm] at hlow
  have hstrict : ENNReal.ofReal (‖v‖ ^ 2 - ε) <
      atTop.liminf (fun n => ENNReal.ofReal (‖F n‖ ^ 2)) :=
    ((ENNReal.ofReal_lt_ofReal_iff hpos).mpr (by linarith)).trans_le hlow
  filter_upwards [eventually_lt_of_lt_liminf hstrict] with n hn
  exact ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by linarith)).mp hn).le

theorem energy_modal_lintegral_le_of_eventual_budget
    (q : ℤ) (μ : Measure ℝ) (F : ℕ → ℝ → CriticalSobolev q)
    (W : ℝ → CriticalSobolev q) (B : ℝ)
    (hF : ∀ n, AEStronglyMeasurable (F n) μ)
    (hc : ∀ᵐ t ∂μ, ∀ k i,
      Tendsto (fun n => criticalCoeff q (F n t) k i)
        atTop (𝓝 (criticalCoeff q (W t) k i)))
    (hb : ∀ᶠ n in atTop,
      (∫⁻ t, ENNReal.ofReal (‖F n t‖ ^ 2) ∂μ) ≤ ENNReal.ofReal B) :
    (∫⁻ t, ENNReal.ofReal (‖W t‖ ^ 2) ∂μ) ≤ ENNReal.ofReal B := by
  calc
    _ ≤ ∫⁻ t, atTop.liminf (fun n => ENNReal.ofReal (‖F n t‖ ^ 2)) ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hc] with t ht
      rw [← criticalExtendedSquare_eq_norm q (W t)]
      exact criticalExtendedSquare_le_liminf q (fun n => F n t)
        (criticalCoeff q (W t)) ht
    _ ≤ atTop.liminf (fun n => ∫⁻ t, ENNReal.ofReal (‖F n t‖ ^ 2) ∂μ) :=
      lintegral_liminf_le' (fun n => ((hF n).norm.pow 2).aemeasurable.ennreal_ofReal)
    _ ≤ ENNReal.ofReal B := liminf_le_of_frequently_le' hb.frequently

theorem ENERGY_MODAL_INTERVAL_BUDGET_LIMIT
    (μ : Measure ℝ) (c : ℝ) (hcpos : 0 < c)
    (F₀ : ℕ → CriticalSobolev 0) (v : CriticalSobolev 0)
    (F₂ : ℕ → ℝ → CriticalSobolev 2) (W : ℝ → CriticalSobolev 2)
    (B : ℕ → ℝ) (b : ℝ)
    (hzero : ∀ k i, Tendsto (fun n => criticalCoeff 0 (F₀ n) k i)
      atTop (𝓝 (criticalCoeff 0 v k i)))
    (hF : ∀ n, AEStronglyMeasurable (F₂ n) μ)
    (hFi : ∀ n, Integrable (fun t => ‖F₂ n t‖ ^ 2) μ)
    (hW : Integrable (fun t => ‖W t‖ ^ 2) μ)
    (htwo : ∀ᵐ t ∂μ, ∀ k i,
      Tendsto (fun n => criticalCoeff 2 (F₂ n t) k i)
        atTop (𝓝 (criticalCoeff 2 (W t) k i)))
    (hbudget : ∀ n, ‖F₀ n‖ ^ 2 + c * (∫ t, ‖F₂ n t‖ ^ 2 ∂μ) ≤ B n)
    (hB : Tendsto B atTop (𝓝 b)) :
    ‖v‖ ^ 2 + c * (∫ t, ‖W t‖ ^ 2 ∂μ) ≤ b := by
  have heps (ε : ℝ) (hε : 0 < ε) :
      ‖v‖ ^ 2 + c * (∫ t, ‖W t‖ ^ 2 ∂μ) ≤ b + 2 * ε := by
    have hupper : ∀ᶠ n in atTop, B n < b + ε :=
      hB.eventually (Iio_mem_nhds (by linarith))
    have hevent : ∀ᶠ n in atTop,
        (∫ t, ‖F₂ n t‖ ^ 2 ∂μ) ≤ (b - ‖v‖ ^ 2 + 2 * ε) / c := by
      filter_upwards [hupper, energy_modal_eventually_lower 0 F₀ v hzero ε hε]
        with n hn hlow
      apply (le_div_iff₀ hcpos).mpr
      have hb := hbudget n
      nlinarith
    have hnonneg : 0 ≤ (b - ‖v‖ ^ 2 + 2 * ε) / c := by
      obtain ⟨n, hn⟩ := hevent.exists
      exact (integral_nonneg (fun t => sq_nonneg ‖F₂ n t‖)).trans hn
    have hlin : ∀ᶠ n in atTop,
        (∫⁻ t, ENNReal.ofReal (‖F₂ n t‖ ^ 2) ∂μ) ≤
          ENNReal.ofReal ((b - ‖v‖ ^ 2 + 2 * ε) / c) := by
      filter_upwards [hevent] with n hn
      rw [← ofReal_integral_eq_lintegral_ofReal (hFi n)
        (Eventually.of_forall (fun t => sq_nonneg ‖F₂ n t‖))]
      exact ENNReal.ofReal_le_ofReal hn
    have hpass := energy_modal_lintegral_le_of_eventual_budget 2 μ F₂ W
      ((b - ‖v‖ ^ 2 + 2 * ε) / c) hF htwo hlin
    rw [← ofReal_integral_eq_lintegral_ofReal hW
      (Eventually.of_forall (fun t => sq_nonneg ‖W t‖))] at hpass
    have hr := (ENNReal.ofReal_le_ofReal_iff hnonneg).mp hpass
    have hm := (le_div_iff₀ hcpos).mp hr
    nlinarith
  by_contra h
  have hpos : 0 < ‖v‖ ^ 2 + c * (∫ t, ‖W t‖ ^ 2 ∂μ) - b := by linarith
  have hsmall := heps ((‖v‖ ^ 2 + c * (∫ t, ‖W t‖ ^ 2 ∂μ) - b) / 4)
    (div_pos hpos (by norm_num))
  linarith

theorem GALERKIN_INTERVAL_ENERGY_IDENTITY
    {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    coefficientEnergy N (g.coeff t) +
      2 * ν * (∫ r in s..t, coefficientDissipation N (g.coeff r)) =
        coefficientEnergy N (g.coeff s) := by
  have hE : ContinuousOn (fun r => coefficientEnergy N (g.coeff r)) (Icc s t) :=
    g.coefficientEnergy_continuousOn.mono (fun r hr => hs.trans hr.1)
  have hD : IntervalIntegrable
      (fun r => (-2 * ν) * coefficientDissipation N (g.coeff r)) volume s t :=
    ((g.coefficientDissipation_continuousOn.mono
      (fun r hr => hs.trans hr.1)).intervalIntegrable_of_Icc hst).const_mul (-2 * ν)
  have hd : ∀ r ∈ Ioo s t,
      HasDerivAt (fun r => coefficientEnergy N (g.coeff r))
        ((-2 * ν) * coefficientDissipation N (g.coeff r)) r := by
    intro r hr
    have hrpos : 0 < r := hs.trans_lt hr.1
    exact (g.coefficientEnergy_identity hrpos.le).hasDerivAt (Ici_mem_nhds hrpos)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hst hE hd hD
  rw [intervalIntegral.integral_const_mul] at hFTC
  linarith

theorem ENERGY_GALERKIN_INTERVAL_LIMIT
    (ν : ℝ) (hν : 0 < ν) (a : ℕ → Field) (N : ℕ → ℕ)
    (g : ∀ n, GalerkinSolution ν (a n) (N n))
    (U : ℝ → TorusSobolev 0) (W : ℝ → CriticalSobolev 2)
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t)
    (hc : ∀ r ∈ Icc s t, ∀ k i,
      Tendsto (fun n => (g n).coeff r k i) atTop (𝓝 ((U r).val k i)))
    (hW : MemLp W 2 (volume.restrict (Icc s t)))
    (hw : ∀ᵐ r ∂volume.restrict (Icc s t), criticalCoeff 2 (W r) = (U r).val)
    (hstart : Tendsto (fun n => coefficientEnergy (N n) ((g n).coeff s))
      atTop (𝓝 (‖U s‖ ^ 2))) :
    ‖U t‖ ^ 2 + 2 * ν * (∫ r in Icc s t, ‖W r‖ ^ 2) ≤ ‖U s‖ ^ 2 := by
  let v := criticalH0Equiv.symm (U t)
  have hv : criticalCoeff 0 v = (U t).val := by
    rw [← criticalH0Equiv_coeff]
    exact congrArg Subtype.val (criticalH0Equiv.apply_symm_apply (U t))
  have hcont (n : ℕ) : ContinuousOn ((g n).criticalState 2) (Icc s t) :=
    ((g n).criticalState_continuousOn 2).mono (fun r hr => hs.trans hr.1)
  have hsq (n : ℕ) (r : ℝ) : ‖(g n).criticalState 2 r‖ ^ 2 =
      coefficientDissipation (N n) ((g n).coeff r) := by
    rw [(g n).criticalState_norm_sq_nat 2 r, criticalEnergy_two_eq_coefficientDissipation]
  have hpass := ENERGY_MODAL_INTERVAL_BUDGET_LIMIT
    (volume.restrict (Icc s t)) (2 * ν) (by positivity)
    (fun n => (g n).criticalState 0 t) v (fun n => (g n).criticalState 2) W
    (fun n => coefficientEnergy (N n) ((g n).coeff s)) (‖U s‖ ^ 2)
    (by
      intro k i
      have heq (n : ℕ) : criticalCoeff 0 ((g n).criticalState 0 t) = (g n).coeff t :=
        (g n).criticalState_coeff 0 (hs.trans hst)
      simpa only [heq, hv] using
        hc t ⟨hst, le_rfl⟩ k i)
    (fun n => (hcont n).aestronglyMeasurable_of_isCompact isCompact_Icc measurableSet_Icc)
    (fun n => ((hcont n).norm.pow 2).integrableOn_compact isCompact_Icc)
    ((memLp_two_iff_integrable_sq_norm hW.aestronglyMeasurable).mp hW)
    (by
      filter_upwards [hw, ae_restrict_mem measurableSet_Icc] with r hr hmem
      intro k i
      have heq (n : ℕ) : criticalCoeff 2 ((g n).criticalState 2 r) = (g n).coeff r :=
        (g n).criticalState_coeff 2 (hs.trans hmem.1)
      simpa only [heq, hr] using hc r hmem k i)
    (by
      intro n
      rw [galerkin_critical_zero_norm_sq]
      simp_rw [hsq]
      have h := GALERKIN_INTERVAL_ENERGY_IDENTITY (g n) hs hst
      rw [intervalIntegral.integral_of_le hst, ← integral_Icc_eq_integral_Ioc] at h
      exact h.le)
    hstart
  simpa only [v, criticalH0Equiv.symm.norm_map] using hpass

end
end QuasiFeffermanB
