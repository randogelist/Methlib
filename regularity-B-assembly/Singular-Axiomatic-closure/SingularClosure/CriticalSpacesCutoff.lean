import SingularClosure.CriticalSpaces

/-! Concrete finite-mode projections and density in every half-order space. -/

set_option autoImplicit false
set_option Elab.async true

open Set Filter
open scoped BigOperators Topology ENNReal

namespace SingularClosure

noncomputable section

/-- Coordinate projection in the explicit weighted ℓ² representation. -/
def criticalLpProjection (S : Finset FourierIndex) :
    FourierVectorSequence →L[ℂ] FourierVectorSequence :=
  ∑ ki ∈ S, (lp.singleContinuousLinearMap ℂ (fun _ : FourierIndex => ℂ) 2 ki).comp
    (lp.evalCLM ℂ (fun _ : FourierIndex => ℂ) 2 ki)

theorem criticalLpProjection_eq_sum (S : Finset FourierIndex) (z : FourierVectorSequence) :
    criticalLpProjection S z = ∑ ki ∈ S, lp.single 2 ki (z ki) := by
  simp [criticalLpProjection]

@[simp]
theorem criticalLpProjection_apply (S : Finset FourierIndex)
    (z : FourierVectorSequence) (ki : FourierIndex) :
    criticalLpProjection S z ki = if ki ∈ S then z ki else 0 := by
  rw [criticalLpProjection_eq_sum]
  simp only [lp.coeFn_sum, Finset.sum_apply, lp.coeFn_single, Finset.sum_pi_single]

theorem criticalLpProjection_norm_le (S : Finset FourierIndex) (z : FourierVectorSequence) :
    ‖criticalLpProjection S z‖ ≤ ‖z‖ := by
  apply lp.norm_mono (by norm_num)
  intro ki
  rw [criticalLpProjection_apply]
  split_ifs with h
  · exact le_rfl
  · simpa only [norm_zero] using norm_nonneg (z ki)

/-- The actual cutoff, retaining the zero mode for arbitrary Sobolev inputs. -/
def criticalSobolevCutoff (q : ℤ) (N : ℕ) : CriticalSobolev q →L[ℂ] CriticalSobolev q :=
  ((criticalSobolevRepr q).symm.toContinuousLinearEquiv.toContinuousLinearMap).comp
    ((criticalLpProjection (sobolevCutoffIndices N)).comp
      (criticalSobolevRepr q).toContinuousLinearEquiv.toContinuousLinearMap)

theorem criticalSobolevCutoff_repr (q : ℤ) (N : ℕ) (c : CriticalSobolev q) :
    criticalSobolevRepr q (criticalSobolevCutoff q N c) =
      criticalLpProjection (sobolevCutoffIndices N) (criticalSobolevRepr q c) := by
  change criticalSobolevRepr q ((criticalSobolevRepr q).symm _) = _
  exact (criticalSobolevRepr q).apply_symm_apply _

@[simp]
theorem criticalSobolevCutoff_coeff (q : ℤ) (N : ℕ) (c : CriticalSobolev q)
    (k : Frequency) (i : Fin 3) :
    criticalCoeff q (criticalSobolevCutoff q N c) k i =
      if k ∈ sobolevCutoffModes N then criticalCoeff q c k i else 0 := by
  classical
  have h := congrArg (fun z : FourierVectorSequence => z (k, i))
    (criticalSobolevCutoff_repr q N c)
  simp only [criticalSobolevRepr_apply, criticalLpProjection_apply,
    sobolevCutoffIndices, Finset.mem_product, Finset.mem_univ, and_true] at h
  apply mul_left_cancel₀ (zpow_ne_zero q (criticalHalfWeight_complex_ne_zero k))
  change criticalWeightedCoeff q (criticalCoeff q (criticalSobolevCutoff q N c)) (k, i) = _
  rw [h]
  by_cases hk : k ∈ sobolevCutoffModes N <;>
    simp only [hk, if_true, if_false, criticalWeightedCoeff, mul_zero]

theorem criticalSobolevCutoff_norm_le (q : ℤ) (N : ℕ) (c : CriticalSobolev q) :
    ‖criticalSobolevCutoff q N c‖ ≤ ‖c‖ := by
  calc
    _ = ‖criticalSobolevRepr q (criticalSobolevCutoff q N c)‖ :=
      ((criticalSobolevRepr q).norm_map _).symm
    _ = ‖criticalLpProjection (sobolevCutoffIndices N) (criticalSobolevRepr q c)‖ :=
      congrArg norm (criticalSobolevCutoff_repr q N c)
    _ ≤ ‖criticalSobolevRepr q c‖ := criticalLpProjection_norm_le _ _
    _ = ‖c‖ := (criticalSobolevRepr q).norm_map c

theorem criticalSobolevCutoff_eq_cutoffCoeff (q : ℤ) (N : ℕ) (c : CriticalSobolev q)
    (hc : SpectralMeanZero (criticalCoeff q c)) :
    criticalCoeff q (criticalSobolevCutoff q N c) = cutoffCoeff N (criticalCoeff q c) := by
  funext k i
  by_cases hk : k = 0
  · subst k
    simp [criticalSobolevCutoff_coeff, cutoffCoeff, hc]
  · simp [criticalSobolevCutoff_coeff, cutoffCoeff, sobolevCutoffModes, hk]

theorem eventually_mem_sobolevCutoffModes (k : Frequency) :
    ∀ᶠ N : ℕ in atTop, k ∈ sobolevCutoffModes N := by
  classical
  by_cases hk : k = 0
  · subst k
    exact Filter.Eventually.of_forall fun N => Finset.mem_insert_self _ _
  · obtain ⟨M, hM⟩ := exists_nat_gt (galerkinFreqSq k)
    filter_upwards [eventually_ge_atTop (M + 1)] with N hN
    apply Finset.mem_insert_of_mem
    apply mem_cutoffModes_of_freqSq_le hk
    have hMN : (M : ℤ) < (N : ℤ) := by exact_mod_cast (by omega : M < N)
    have hNpos : (1 : ℤ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
    nlinarith [sq_nonneg ((N : ℤ) - 1)]

theorem sobolevCutoffIndices_tendsto_atTop :
    Tendsto sobolevCutoffIndices atTop atTop := by
  classical
  apply tendsto_atTop.2
  intro S
  apply (eventually_all_finset S).2
  intro ki hki
  filter_upwards [eventually_mem_sobolevCutoffModes ki.1] with N hN
  exact Finset.mem_product.mpr ⟨hN, Finset.mem_univ _⟩

/-- The actual finite cutoffs converge in the full weighted Hilbert norm. -/
theorem criticalSobolevCutoff_tendsto (q : ℤ) (c : CriticalSobolev q) :
    Tendsto (fun N : ℕ => criticalSobolevCutoff q N c) atTop (𝓝 c) := by
  have hsum : Tendsto
      (fun N : ℕ => criticalLpProjection (sobolevCutoffIndices N) (criticalSobolevRepr q c))
      atTop (𝓝 (criticalSobolevRepr q c)) := by
    have h : Tendsto
        (fun S : Finset FourierIndex => ∑ ki ∈ S, lp.single 2 ki (criticalSobolevRepr q c ki))
        atTop (𝓝 (criticalSobolevRepr q c)) :=
      lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ∞) (criticalSobolevRepr q c)
    simpa only [criticalLpProjection_eq_sum, Function.comp_def] using
      h.comp sobolevCutoffIndices_tendsto_atTop
  have h := (criticalSobolevRepr q).symm.continuous.continuousAt.tendsto.comp hsum
  change Tendsto (fun N : ℕ => (criticalSobolevRepr q).symm
    (criticalLpProjection (sobolevCutoffIndices N) (criticalSobolevRepr q c))) atTop (𝓝 c)
  simpa only [Function.comp_def, (criticalSobolevRepr q).symm_apply_apply] using h

/-- Every literal finite coefficient cutoff belongs to every half-order space. -/
theorem cutoffCoeff_mem_criticalSobolev (q : ℤ) (N : ℕ) (c : FourierCoeff) :
    Memℓp (criticalWeightedCoeff q (cutoffCoeff N c)) 2 := by
  apply Memℓp.of_exponent_ge (q := 0) _ (by norm_num)
  apply memℓp_zero
  apply ((cutoffModes N).product (Finset.univ : Finset (Fin 3))).finite_toSet.subset
  intro ki hki
  by_contra hnot
  have hk : ki.1 ∉ cutoffModes N := by simpa using hnot
  exact hki (by simp [criticalWeightedCoeff, cutoffCoeff, hk])

def criticalFiniteSobolev (q : ℤ) (N : ℕ) (c : FourierCoeff) : CriticalSobolev q :=
  criticalSobolevOfCoeff q (cutoffCoeff N c) (cutoffCoeff_mem_criticalSobolev q N c)

@[simp]
theorem criticalFiniteSobolev_coeff (q : ℤ) (N : ℕ) (c : FourierCoeff) :
    criticalCoeff q (criticalFiniteSobolev q N c) = cutoffCoeff N c :=
  criticalSobolevOfCoeff_coeff q (cutoffCoeff N c) (cutoffCoeff_mem_criticalSobolev q N c)

theorem criticalFiniteSobolev_eq_projection (q : ℤ) (N : ℕ) (c : CriticalSobolev q)
    (hc : SpectralMeanZero (criticalCoeff q c)) :
    criticalFiniteSobolev q N (criticalCoeff q c) = criticalSobolevCutoff q N c := by
  apply criticalCoeff_injective q
  rw [criticalFiniteSobolev_coeff, criticalSobolevCutoff_eq_cutoffCoeff q N c hc]

theorem criticalFiniteSobolev_norm_le (q : ℤ) (N : ℕ) (c : CriticalSobolev q)
    (hc : SpectralMeanZero (criticalCoeff q c)) :
    ‖criticalFiniteSobolev q N (criticalCoeff q c)‖ ≤ ‖c‖ := by
  rw [criticalFiniteSobolev_eq_projection q N c hc]
  exact criticalSobolevCutoff_norm_le q N c

theorem criticalFiniteSobolev_tendsto (q : ℤ) (c : CriticalSobolev q)
    (hc : SpectralMeanZero (criticalCoeff q c)) :
    Tendsto (fun N => criticalFiniteSobolev q N (criticalCoeff q c)) atTop (𝓝 c) := by
  simpa only [criticalFiniteSobolev_eq_projection q _ c hc] using
    criticalSobolevCutoff_tendsto q c

theorem criticalFiniteSobolev_norm_sq (q : ℤ) (N : ℕ) (c : FourierCoeff) :
    ‖criticalFiniteSobolev q N c‖ ^ 2 =
      ∑ k ∈ cutoffModes N, ∑ i : Fin 3,
        criticalFrequencyWeight k ^ q * Complex.normSq (c k i) := by
  rw [criticalSobolev_norm_sq, criticalFiniteSobolev_coeff]
  let S : Finset FourierIndex := (cutoffModes N).product Finset.univ
  have htail : ∀ ki : FourierIndex, ki ∉ S →
      criticalFrequencyWeight ki.1 ^ q * Complex.normSq (cutoffCoeff N c ki.1 ki.2) = 0 := by
    intro ki hki
    have hk : ki.1 ∉ cutoffModes N := by simpa [S] using hki
    simp [cutoffCoeff, hk]
  rw [tsum_eq_sum htail]
  calc
    _ = ∑ k ∈ cutoffModes N, ∑ i : Fin 3,
        criticalFrequencyWeight k ^ q * Complex.normSq (cutoffCoeff N c k i) :=
      Finset.sum_product (cutoffModes N) Finset.univ
        (fun ki : FourierIndex => criticalFrequencyWeight ki.1 ^ q *
          Complex.normSq (cutoffCoeff N c ki.1 ki.2))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro i hi
      simp only [cutoffCoeff, if_pos hk]

end

end SingularClosure
