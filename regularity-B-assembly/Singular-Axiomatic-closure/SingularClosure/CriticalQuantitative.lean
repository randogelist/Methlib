import SingularClosure.CriticalUniformBounds
import SingularClosure.CriticalLimitRepresentatives

/-! Quantitative bounds of the actual rough-data limit. The terminal critical
energy and the quartic H1 integral are passed to the limit together. -/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory Filter
open scoped BigOperators Topology Interval ENNReal

namespace SingularClosure
noncomputable section

/-- Addition preserves the lower Fatou bound, including infinite values. -/
theorem critical_ennreal_liminf_add_le (f g : ℕ → ℝ≥0∞) :
    atTop.liminf f + atTop.liminf g ≤ atTop.liminf (fun n => f n + g n) := by
  by_cases hf : atTop.liminf f = 0
  · rw [hf, zero_add]
    exact Filter.liminf_le_liminf (Filter.Eventually.of_forall (fun n => le_add_left le_rfl))
  by_cases hg : atTop.liminf g = 0
  · rw [hg, add_zero]
    exact Filter.liminf_le_liminf (Filter.Eventually.of_forall (fun n => le_add_right le_rfl))
  apply (Filter.le_liminf_iff).2
  intro c hc
  obtain ⟨b, hb, d, hd, hbd⟩ := ENNReal.exists_lt_add_of_lt_add hc hf hg
  filter_upwards [Filter.eventually_lt_of_lt_liminf hb,
    Filter.eventually_lt_of_lt_liminf hd] with n hn hm
  exact hbd.trans (ENNReal.add_lt_add hn hm)

/-- Modal lower semicontinuity of the fourth power of a homogeneous norm. -/
theorem criticalExtendedQuartic_le_liminf (q : ℤ)
    (F : ℕ → CriticalSobolev q) (c : FourierCoeff)
    (hcoeff : ∀ k i, Tendsto (fun n => criticalCoeff q (F n) k i) atTop (𝓝 (c k i))) :
    criticalExtendedSquare q c ^ 2 ≤
      atTop.liminf (fun n => ENNReal.ofReal (‖F n‖ ^ 4)) := by
  have h := criticalExtendedSquare_le_liminf q F c hcoeff
  calc
    _ ≤ (atTop.liminf (fun n => ENNReal.ofReal (‖F n‖ ^ 2))) ^ 2 := by gcongr
    _ ≤ atTop.liminf (fun n => ENNReal.ofReal (‖F n‖ ^ 2) ^ 2) := by
      simpa only [pow_two, Pi.mul_apply] using
        (ENNReal.le_liminf_mul
          (u := fun n => ENNReal.ofReal (‖F n‖ ^ 2))
          (v := fun n => ENNReal.ofReal (‖F n‖ ^ 2)) (f := atTop))
    _ = _ := by
      congr 1
      funext n
      rw [← ENNReal.ofReal_pow (sq_nonneg _) 2, ← pow_mul]

/-- Joint terminal-energy and integrated-energy Fatou inequality. Its right
side is the actual common finite-dimensional budget, not a limit premise. -/
theorem critical_modal_quartic_budget
    (q r : ℤ) (T δ A : ℝ) (hT : 0 ≤ T) (hδ : 0 ≤ δ)
    (F : ℕ → ℝ → CriticalSobolev q) (G : ℕ → CriticalSobolev r)
    (c : ℝ → FourierCoeff) (d : FourierCoeff)
    (hF : ∀ n, ContinuousOn (F n) (Icc (0 : ℝ) T))
    (hcoeff : ∀ t ∈ Icc (0 : ℝ) T, ∀ k i,
      Tendsto (fun n => criticalCoeff q (F n t) k i) atTop (𝓝 (c t k i)))
    (hterminal : ∀ k i,
      Tendsto (fun n => criticalCoeff r (G n) k i) atTop (𝓝 (d k i)))
    (hbudget : ∀ n, ‖G n‖ ^ 4 + δ * (∫ t in (0 : ℝ)..T, ‖F n t‖ ^ 4) ≤ A) :
    criticalExtendedSquare r d ^ 2 + ENNReal.ofReal δ *
      (∫⁻ t in Icc (0 : ℝ) T, criticalExtendedSquare q (c t) ^ 2) ≤
        ENNReal.ofReal A := by
  let μ : Measure ℝ := volume.restrict (Icc (0 : ℝ) T)
  let J : ℕ → ℝ≥0∞ := fun n => ∫⁻ t, ENNReal.ofReal (‖F n t‖ ^ 4) ∂μ
  have hterm := criticalExtendedQuartic_le_liminf r G d hterminal
  have hint : (∫⁻ t, criticalExtendedSquare q (c t) ^ 2 ∂μ) ≤ atTop.liminf J := by
    calc
      _ ≤ ∫⁻ t, atTop.liminf (fun n => ENNReal.ofReal (‖F n t‖ ^ 4)) ∂μ := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
        exact criticalExtendedQuartic_le_liminf q (fun n => F n t) (c t) (hcoeff t ht)
      _ ≤ atTop.liminf J := lintegral_liminf_le' (fun n =>
        (((hF n).norm.pow 4).aestronglyMeasurable_of_isCompact
          isCompact_Icc measurableSet_Icc).aemeasurable.ennreal_ofReal)
  have hmul : ENNReal.ofReal δ * atTop.liminf J ≤
      atTop.liminf (fun n => ENNReal.ofReal δ * J n) := by
    simpa only [Filter.liminf_const, Pi.mul_apply] using
      (ENNReal.le_liminf_mul (u := fun _ : ℕ => ENNReal.ofReal δ) (v := J) (f := atTop))
  have htotal (n : ℕ) : ENNReal.ofReal (‖G n‖ ^ 4) + ENNReal.ofReal δ * J n ≤
      ENNReal.ofReal A := by
    have hi : Integrable (fun t => ‖F n t‖ ^ 4) μ :=
      ((hF n).norm.pow 4).integrableOn_compact isCompact_Icc
    have heq := ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall (fun t => pow_nonneg (norm_nonneg (F n t)) 4))
    have hI : 0 ≤ ∫ t, ‖F n t‖ ^ 4 ∂μ :=
      integral_nonneg (fun t => pow_nonneg (norm_nonneg (F n t)) 4)
    change ENNReal.ofReal (‖G n‖ ^ 4) + ENNReal.ofReal δ *
      (∫⁻ t, ENNReal.ofReal (‖F n t‖ ^ 4) ∂μ) ≤ _
    rw [← heq, ← ENNReal.ofReal_mul hδ,
      ← ENNReal.ofReal_add (pow_nonneg (norm_nonneg _) 4) (mul_nonneg hδ hI)]
    apply ENNReal.ofReal_le_ofReal
    have h := hbudget n
    rw [intervalIntegral.integral_of_le hT, ← integral_Icc_eq_integral_Ioc] at h
    exact h
  calc
    _ ≤ atTop.liminf (fun n => ENNReal.ofReal (‖G n‖ ^ 4)) +
        ENNReal.ofReal δ * atTop.liminf J := by gcongr
    _ ≤ atTop.liminf (fun n => ENNReal.ofReal (‖G n‖ ^ 4)) +
        atTop.liminf (fun n => ENNReal.ofReal δ * J n) := add_le_add_left hmul _
    _ ≤ atTop.liminf (fun n => ENNReal.ofReal (‖G n‖ ^ 4) + ENNReal.ofReal δ * J n) :=
      critical_ennreal_liminf_add_le _ _
    _ ≤ ENNReal.ofReal A :=
      liminf_le_of_frequently_le' (Filter.Frequently.of_forall htotal)

/-- The sharp factor four survives the actual Galerkin limit. No strong
critical convergence at the terminal time is required. -/
theorem SMALL_DATA_LIMIT_SHARP_QUARTIC
    (ν : ℝ) (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hsmall : criticalNonlinearConstant * ‖a‖ < ν)
    (φ : ℕ → ℕ)
    (g : ∀ n, GalerkinSolution ν
      (finiteSynthesis (φ n + 1) (criticalCoeff 1 a)) (φ n + 1))
    (u : ℝ → CriticalSobolev 1) (T : ℝ) (hT : 0 ≤ T)
    (hconv : TendstoUniformlyOn (fun n t => (g n).sobolevState 0 t)
      (fun t => criticalToTorusH0 1 (by norm_num) (u t)) atTop (Icc (0 : ℝ) T)) :
    ENNReal.ofReal (‖u T‖ ^ 4) +
      ENNReal.ofReal (4 * (ν - criticalNonlinearConstant * ‖a‖)) *
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
      (4 * (ν - criticalNonlinearConstant * ‖a‖)) *
        (∫ t in (0 : ℝ)..T, ‖(g n).criticalState 2 t‖ ^ 4) ≤ ‖a‖ ^ 4 := by
    have h := criticalGalerkin_sharp_square_budget a hreal hsmall hT (g n)
    have hp : 0 < 4 * (ν - criticalNonlinearConstant * ‖a‖) :=
      mul_pos (by norm_num) (sub_pos.mpr hsmall)
    have hmul := (le_div_iff₀ hp).mp h
    have hfour (q : ℕ) (t : ℝ) : ‖(g n).criticalState (q : ℤ) t‖ ^ 4 =
        criticalEnergy q (φ n + 1) ((g n).coeff t) ^ 2 := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, (g n).criticalState_norm_sq_nat q t]
    simp_rw [hfour, criticalEnergy_two_eq_coefficientDissipation]
    nlinarith
  have h := critical_modal_quartic_budget 2 1 T
    (4 * (ν - criticalNonlinearConstant * ‖a‖)) (‖a‖ ^ 4) hT
    (mul_nonneg (by norm_num) (sub_pos.mpr hsmall).le)
    (fun n => (g n).criticalState 2) (fun n => (g n).criticalState 1 T)
    (fun t => criticalCoeff 1 (u t)) (criticalCoeff 1 (u T))
    (fun n => ((g n).criticalState_continuousOn 2).mono (fun t ht => ht.1))
    (hcoeff 2) (hcoeff 1 T ⟨hT, le_rfl⟩) hbudget
  rw [criticalExtendedSquare_eq_norm,
    ← ENNReal.ofReal_pow (sq_nonneg _) 2, ← pow_mul] at h
  exact h

/-- The actual negative-half RHS representative retains its explicit budget. -/
theorem SMALL_DATA_LIMIT_NEGATIVE_HALF
    (ν : ℝ) (hν : 0 ≤ ν) (a : CriticalSobolev 1)
    (hreal : SpectralReality (criticalCoeff 1 a))
    (hsmall : criticalNonlinearConstant * ‖a‖ < ν)
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
      (∫ t in Icc (0 : ℝ) T, ‖V t‖ ^ 2) ≤ criticalTimeDerivativeBudget ν a := by
  exact criticalGalerkinLimit_rhs_memLp ν
    (fun n => finiteSynthesis (φ n + 1) (criticalCoeff 1 a)) φ hφ g
    (fun t => criticalToTorusH0 1 (by norm_num) (u t)) (-1) T
    (criticalTimeDerivativeBudget ν a) hT (criticalTimeDerivativeBudget_nonneg a hsmall)
    hu hconv (fun n => CRITICAL_GALERKIN_TIME_DERIVATIVE_BUDGET hν a hreal hsmall hT (g n))

end
end SingularClosure
