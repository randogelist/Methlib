import SingularClosure.CriticalLimitGlobal
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Function.L2Space

/-! Bochner representatives from joint time/Fourier Fatou bounds.

The extended squared Fourier norm is defined before membership is known.
Fatou's lemma proves it finite almost everywhere. Finite Fourier projections
then construct a strongly measurable representative in the actual weighted
Hilbert space, with the inherited L2 time budget.
-/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory Filter
open scoped BigOperators Topology Interval ENNReal

namespace SingularClosure

noncomputable section

def criticalExtendedSquare (q : ℤ) (c : FourierCoeff) : ℝ≥0∞ :=
  ∑' ki : FourierIndex, ENNReal.ofReal (‖criticalWeightedCoeff q c ki‖ ^ 2)

theorem criticalWeighted_square_summable (q : ℤ) (v : CriticalSobolev q) :
    Summable (fun ki : FourierIndex => ‖criticalWeightedCoeff q (criticalCoeff q v) ki‖ ^ 2) := by
  have h := (memℓp_gen_iff (p := (2 : ℝ≥0∞)) (by norm_num)).mp (criticalCoeff_mem q v)
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h

theorem criticalExtendedSquare_eq_norm (q : ℤ) (v : CriticalSobolev q) :
    criticalExtendedSquare q (criticalCoeff q v) = ENNReal.ofReal (‖v‖ ^ 2) := by
  have h := lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num) (criticalSobolevRepr q v)
  have hn : ‖v‖ ^ 2 = ∑' ki : FourierIndex,
      ‖criticalWeightedCoeff q (criticalCoeff q v) ki‖ ^ 2 := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two,
      (criticalSobolevRepr q).norm_map, criticalSobolevRepr_apply] using h
  rw [criticalExtendedSquare, ← ENNReal.ofReal_tsum_of_nonneg
    (fun ki => sq_nonneg _) (criticalWeighted_square_summable q v), ← hn]

theorem criticalExtendedSquare_finite_mem (q : ℤ) (c : FourierCoeff)
    (h : criticalExtendedSquare q c ≠ ∞) : Memℓp (criticalWeightedCoeff q c) 2 := by
  have hs := ENNReal.summable_toReal h
  have hs' : Summable (fun ki : FourierIndex => ‖criticalWeightedCoeff q c ki‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofReal (sq_nonneg _)] using hs
  apply (memℓp_gen_iff (p := (2 : ℝ≥0∞)) (by norm_num)).mpr
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hs'

/-- Lower semicontinuity in the literal coefficient topology, before Sobolev membership. -/
theorem criticalExtendedSquare_le_liminf (q : ℤ)
    (F : ℕ → CriticalSobolev q) (c : FourierCoeff)
    (hcoeff : ∀ k i, Tendsto (fun n => criticalCoeff q (F n) k i) atTop (𝓝 (c k i))) :
    criticalExtendedSquare q c ≤
      atTop.liminf (fun n => ENNReal.ofReal (‖F n‖ ^ 2)) := by
  classical
  rw [criticalExtendedSquare, ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro S
  have hsum : Tendsto (fun n => ∑ ki ∈ S,
      ENNReal.ofReal (‖criticalWeightedCoeff q (criticalCoeff q (F n)) ki‖ ^ 2)) atTop
      (𝓝 (∑ ki ∈ S, ENNReal.ofReal (‖criticalWeightedCoeff q c ki‖ ^ 2))) := by
    apply tendsto_finset_sum
    intro ki hki
    have h := ((hcoeff ki.1 ki.2).const_mul ((criticalHalfWeight ki.1 : ℂ) ^ q)).norm.pow 2
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp h
  rw [← hsum.liminf_eq]
  apply Filter.liminf_le_liminf
  apply Filter.Eventually.of_forall
  intro n
  rw [← criticalExtendedSquare_eq_norm q (F n)]
  exact ENNReal.sum_le_tsum S

theorem criticalFiniteSobolev_curve_continuousOn
    (q : ℤ) (K : ℕ) (c : ℝ → FourierCoeff) (S : Set ℝ)
    (hc : ∀ k i, ContinuousOn (fun t => c t k i) S) :
    ContinuousOn (fun t => criticalFiniteSobolev q K (c t)) S := by
  have hfinite : ContinuousOn (fun t => restrictFiniteState K (c t)) S := by
    apply continuousOn_pi.mpr
    intro k
    apply continuousOn_pi.mpr
    intro i
    exact hc k.val i
  have h := (criticalFiniteState q K).continuous.comp_continuousOn hfinite
  simpa only [Function.comp_def, criticalFiniteState_restrict] using! h

/-- A modal limit of bounded L2-time Sobolev trajectories has an actual
Bochner L2 representative of the same order and the inherited energy budget.
The zero-frequency premise is the literal mean-zero constraint. -/
theorem critical_memLp_realization_of_modal_limit
    (q : ℤ) (T B : ℝ) (hT : 0 ≤ T) (hB : 0 ≤ B)
    (F : ℕ → ℝ → CriticalSobolev q) (c : ℝ → FourierCoeff)
    (hF : ∀ n, ContinuousOn (F n) (Icc (0 : ℝ) T))
    (hc : ∀ k i, ContinuousOn (fun t => c t k i) (Icc (0 : ℝ) T))
    (hzero : ∀ t ∈ Icc (0 : ℝ) T, SpectralMeanZero (c t))
    (hbudget : ∀ n, (∫ t in (0 : ℝ)..T, ‖F n t‖ ^ 2) ≤ B)
    (hcoeff : ∀ t ∈ Icc (0 : ℝ) T, ∀ k i,
      Tendsto (fun n => criticalCoeff q (F n t) k i) atTop (𝓝 (c t k i))) :
    ∃ v : ℝ → CriticalSobolev q,
      MemLp v 2 (volume.restrict (Icc (0 : ℝ) T)) ∧
      (∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T), criticalCoeff q (v t) = c t) ∧
      (∫ t in Icc (0 : ℝ) T, ‖v t‖ ^ 2) ≤ B := by
  classical
  let μ : Measure ℝ := volume.restrict (Icc (0 : ℝ) T)
  have hFmeas (n : ℕ) : AEStronglyMeasurable (F n) μ :=
    (hF n).aestronglyMeasurable_of_isCompact isCompact_Icc measurableSet_Icc
  have hEmeas : AEMeasurable (fun t => criticalExtendedSquare q (c t)) μ := by
    apply AEMeasurable.tsum
    intro ki
    have hm := ((hc ki.1 ki.2).const_mul ((criticalHalfWeight ki.1 : ℂ) ^ q)).norm.pow 2
    exact (hm.aestronglyMeasurable_of_isCompact isCompact_Icc measurableSet_Icc).
      aemeasurable.ennreal_ofReal
  have hlin (n : ℕ) : (∫⁻ t, ENNReal.ofReal (‖F n t‖ ^ 2) ∂μ) ≤ ENNReal.ofReal B := by
    have hi : Integrable (fun t => ‖F n t‖ ^ 2) μ :=
      ((hF n).norm.pow 2).integrableOn_compact isCompact_Icc
    have heq := ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall (fun t => sq_nonneg (‖F n t‖)))
    rw [← heq]
    apply ENNReal.ofReal_le_ofReal
    have h := hbudget n
    rw [intervalIntegral.integral_of_le hT, ← integral_Icc_eq_integral_Ioc] at h
    exact h
  have hEbound : (∫⁻ t, criticalExtendedSquare q (c t) ∂μ) ≤ ENNReal.ofReal B := by
    calc
      _ ≤ ∫⁻ t, atTop.liminf (fun n => ENNReal.ofReal (‖F n t‖ ^ 2)) ∂μ := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
        exact criticalExtendedSquare_le_liminf q (fun n => F n t) (c t) (hcoeff t ht)
      _ ≤ atTop.liminf (fun n => ∫⁻ t, ENNReal.ofReal (‖F n t‖ ^ 2) ∂μ) :=
        lintegral_liminf_le' (fun n => ((hFmeas n).norm.pow 2).aemeasurable.ennreal_ofReal)
      _ ≤ ENNReal.ofReal B :=
        liminf_le_of_frequently_le' (Filter.Frequently.of_forall hlin)
  have hfinite : ∀ᵐ t ∂μ, criticalExtendedSquare q (c t) < ∞ :=
    ae_lt_top' hEmeas (hEbound.trans_lt ENNReal.ofReal_lt_top)
  let v : ℝ → CriticalSobolev q := fun t =>
    if hm : Memℓp (criticalWeightedCoeff q (c t)) 2 then criticalSobolevOfCoeff q (c t) hm else 0
  have hraw : ∀ᵐ t ∂μ, criticalCoeff q (v t) = c t := by
    filter_upwards [hfinite] with t ht
    have hm := criticalExtendedSquare_finite_mem q (c t) ht.ne
    change criticalCoeff q (if hm : Memℓp (criticalWeightedCoeff q (c t)) 2 then
      criticalSobolevOfCoeff q (c t) hm else 0) = c t
    rw [dif_pos hm, criticalSobolevOfCoeff_coeff]
  have hprojection (K : ℕ) : AEStronglyMeasurable
      (fun t => criticalFiniteSobolev q K (c t)) μ :=
    (criticalFiniteSobolev_curve_continuousOn q K c (Icc (0 : ℝ) T) hc).
      aestronglyMeasurable_of_isCompact isCompact_Icc measurableSet_Icc
  have htendsto : ∀ᵐ t ∂μ, Tendsto (fun K => criticalFiniteSobolev q K (c t)) atTop (𝓝 (v t)) := by
    filter_upwards [hraw, ae_restrict_mem measurableSet_Icc] with t ht hmem
    have hmean : SpectralMeanZero (criticalCoeff q (v t)) := by
      rw [ht]
      exact hzero t hmem
    simpa only [ht] using criticalFiniteSobolev_tendsto q (v t) hmean
  have hvmeas : AEStronglyMeasurable v μ :=
    aestronglyMeasurable_of_tendsto_ae atTop hprojection htendsto
  have hnormE : (fun t => ENNReal.ofReal (‖v t‖ ^ 2)) =ᵐ[μ]
      (fun t => criticalExtendedSquare q (c t)) := by
    filter_upwards [hraw] with t ht
    rw [← criticalExtendedSquare_eq_norm q (v t), ht]
  have hnormlin : (∫⁻ t, ENNReal.ofReal (‖v t‖ ^ 2) ∂μ) ≤ ENNReal.ofReal B := by
    rw [lintegral_congr_ae hnormE]
    exact hEbound
  have hintegrable : Integrable (fun t => ‖v t‖ ^ 2) μ := by
    refine ⟨hvmeas.norm.pow 2, ?_⟩
    change (∫⁻ t, ‖‖v t‖ ^ 2‖ₑ ∂μ) < ∞
    simp only [Real.enorm_eq_ofReal (sq_nonneg _)]
    exact hnormlin.trans_lt ENNReal.ofReal_lt_top
  refine ⟨v, (memLp_two_iff_integrable_sq_norm hvmeas).mpr hintegrable, hraw, ?_⟩
  have heq := ofReal_integral_eq_lintegral_ofReal hintegrable
    (Filter.Eventually.of_forall (fun t => sq_nonneg (‖v t‖)))
  rw [← heq] at hnormlin
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hnormlin
  rw [ENNReal.toReal_ofReal (integral_nonneg (fun t => sq_nonneg _)),
    ENNReal.toReal_ofReal hB] at hreal
  exact hreal

end

end SingularClosure
