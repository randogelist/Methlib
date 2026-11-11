import SingularClosure.CriticalTraceBand
import SingularClosure.CriticalSpacesCutoff

/-! Finite Fourier bands as actual elements of the critical Hilbert spaces. -/

set_option autoImplicit false

open Set MeasureTheory Filter
open scoped BigOperators Topology ENNReal

namespace SingularClosure

noncomputable section

/-- A finite coefficient array realized in the complete weighted Hilbert space. -/
def criticalBandSobolev (q : ℤ) (s : Finset FourierIndex) (c : FourierCoeff) :
    CriticalSobolev q :=
  (criticalSobolevRepr q).symm
    (∑ ki ∈ s, lp.single 2 ki (criticalWeightedCoeff q c ki))

theorem criticalBandSobolev_repr (q : ℤ) (s : Finset FourierIndex) (c : FourierCoeff) :
    criticalSobolevRepr q (criticalBandSobolev q s c) =
      ∑ ki ∈ s, lp.single 2 ki (criticalWeightedCoeff q c ki) :=
  (criticalSobolevRepr q).apply_symm_apply _

@[simp]
theorem criticalBandSobolev_coeff (q : ℤ) (s : Finset FourierIndex) (c : FourierCoeff)
    (k : Frequency) (i : Fin 3) :
    criticalCoeff q (criticalBandSobolev q s c) k i =
      if (k, i) ∈ s then c k i else 0 := by
  classical
  have h := congrArg (fun z : FourierVectorSequence => z (k, i))
    (criticalBandSobolev_repr q s c)
  simp only [criticalSobolevRepr_apply, lp.coeFn_sum, Finset.sum_apply,
    lp.coeFn_single, Finset.sum_pi_single] at h
  apply mul_left_cancel₀ (zpow_ne_zero q (criticalHalfWeight_complex_ne_zero k))
  by_cases hki : (k, i) ∈ s
  · simpa only [criticalWeightedCoeff, if_pos hki] using h
  · simpa only [criticalWeightedCoeff, if_neg hki, mul_zero] using h

/-- No norm conversion factor is introduced by the Hilbert realization. -/
theorem criticalBandSobolev_norm_sq (q : ℤ) (s : Finset FourierIndex) (c : FourierCoeff) :
    ‖criticalBandSobolev q s c‖ ^ 2 = ‖criticalFiniteBandState q s c‖ ^ 2 := by
  rw [← (criticalSobolevRepr q).norm_map, criticalBandSobolev_repr,
    EuclideanSpace.norm_sq_eq]
  change ‖∑ ki ∈ s, lp.single 2 ki (criticalWeightedCoeff q c ki)‖ ^ 2 =
    ∑ ki : ↥s, ‖criticalWeightedCoeff q c ki.val‖ ^ 2
  rw [Finset.sum_coe_sort]
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    lp.norm_sum_single (p := (2 : ℝ≥0∞)) (by norm_num)
      (criticalWeightedCoeff q c) s

theorem criticalBandSobolev_norm (q : ℤ) (s : Finset FourierIndex) (c : FourierCoeff) :
    ‖criticalBandSobolev q s c‖ = ‖criticalFiniteBandState q s c‖ := by
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    (criticalBandSobolev_norm_sq q s c)

/-- Every finite-band norm is bounded by the full norm at the same order. -/
theorem criticalFiniteBandState_norm_le (q : ℤ) (s : Finset FourierIndex)
    (u : CriticalSobolev q) :
    ‖criticalFiniteBandState q s (criticalCoeff q u)‖ ≤ ‖u‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.norm_sq_eq]
  change (∑ ki : ↥s, ‖criticalWeightedCoeff q (criticalCoeff q u) ki.val‖ ^ 2) ≤ _
  rw [Finset.sum_coe_sort]
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, criticalSobolevRepr_apply,
    (criticalSobolevRepr q).norm_map] using
    lp.sum_rpow_le_norm_rpow (p := (2 : ℝ≥0∞)) (by norm_num)
      (criticalSobolevRepr q u) s

/-- Coordinate continuity suffices for continuity of every finite cutoff. -/
theorem criticalBandSobolev_continuousOn (q : ℤ) (s : Finset FourierIndex)
    (c : ℝ → FourierCoeff) (I : Set ℝ)
    (hc : ∀ ki ∈ s, ContinuousOn (fun t => c t ki.1 ki.2) I) :
    ContinuousOn (fun t => criticalBandSobolev q s (c t)) I := by
  apply (criticalSobolevRepr q).symm.continuous.comp_continuousOn
  apply continuousOn_finset_sum
  intro ki hki
  exact (lp.singleContinuousLinearMap ℂ (fun _ : FourierIndex => ℂ) 2 ki).continuous.comp_continuousOn
    (continuousOn_const.mul (hc ki hki))

/-- For an actual Sobolev vector this is exactly its Fourier cutoff. -/
theorem criticalBandSobolev_eq_cutoff (q : ℤ) (N : ℕ) (u : CriticalSobolev q) :
    criticalBandSobolev q (sobolevCutoffIndices N) (criticalCoeff q u) =
      criticalSobolevCutoff q N u := by
  apply criticalCoeff_injective q
  funext k i
  simp only [criticalBandSobolev_coeff, criticalSobolevCutoff_coeff,
    sobolevCutoffIndices, Finset.mem_product, Finset.mem_univ, and_true]

theorem criticalBandSobolev_initial_tendsto (q : ℤ) (a : CriticalSobolev q) :
    Tendsto (fun N => criticalBandSobolev q (sobolevCutoffIndices N) (criticalCoeff q a))
      atTop (𝓝 a) := by
  simpa only [criticalBandSobolev_eq_cutoff] using criticalSobolevCutoff_tendsto q a

end

end SingularClosure
