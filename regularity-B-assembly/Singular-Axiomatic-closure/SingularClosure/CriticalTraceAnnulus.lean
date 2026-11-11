import SingularClosure.CriticalTraceFourier
import SingularClosure.CriticalTraceTail
import SingularClosure.CriticalSpacesEmbedding

/-! Actual annular cutoff differences and their same-order tail bounds. -/

set_option autoImplicit false

open Set MeasureTheory Filter
open scoped BigOperators Topology ENNReal Interval

namespace SingularClosure

noncomputable section

theorem criticalTrace_cutoffModes_mono {K L : ℕ} (hKL : K ≤ L) :
    sobolevCutoffModes K ⊆ sobolevCutoffModes L := by
  classical
  intro k hk
  rcases Finset.mem_insert.mp hk with rfl | hk
  · exact Finset.mem_insert_self _ _
  · apply Finset.mem_insert_of_mem
    obtain ⟨_, hk0, hkK⟩ := (mem_cutoffModes_iff K k).mp hk
    apply mem_cutoffModes_of_freqSq_le hk0
    have hKL' : (K : ℤ) ≤ L := by exact_mod_cast hKL
    have hK : (0 : ℤ) ≤ K := Int.natCast_nonneg K
    nlinarith

theorem criticalTrace_cutoffIndices_mono {K L : ℕ} (hKL : K ≤ L) :
    sobolevCutoffIndices K ⊆ sobolevCutoffIndices L := by
  intro ki hki
  rcases Finset.mem_product.mp hki with ⟨hk, hi⟩
  exact Finset.mem_product.mpr ⟨criticalTrace_cutoffModes_mono hKL hk, hi⟩

def criticalFourierAnnulus (K L : ℕ) : Finset FourierIndex :=
  sobolevCutoffIndices L \ sobolevCutoffIndices K

/-- An ordered cutoff difference is its literal annular Fourier band. -/
theorem criticalBandSobolev_sub_eq_annulus (q : ℤ) {K L : ℕ} (hKL : K ≤ L)
    (c : FourierCoeff) :
    criticalBandSobolev q (sobolevCutoffIndices L) c -
      criticalBandSobolev q (sobolevCutoffIndices K) c =
      criticalBandSobolev q (criticalFourierAnnulus K L) c := by
  classical
  apply criticalCoeff_injective q
  funext k i
  change criticalCoeff q (criticalBandSobolev q (sobolevCutoffIndices L) c) k i -
    criticalCoeff q (criticalBandSobolev q (sobolevCutoffIndices K) c) k i = _
  simp only [criticalBandSobolev_coeff, criticalFourierAnnulus, Finset.mem_sdiff]
  by_cases hK : (k, i) ∈ sobolevCutoffIndices K
  · have hL := criticalTrace_cutoffIndices_mono hKL hK
    simp only [hK, hL, if_true, not_true_eq_false, and_false, if_false, sub_self]
  · by_cases hL : (k, i) ∈ sobolevCutoffIndices L <;> simp [hK, hL]

/-- A band supported above N sees only the actual N-tail. -/
theorem criticalFiniteBandState_eq_tail (q : ℤ) (s : Finset FourierIndex) (N : ℕ)
    (hs : ∀ ki ∈ s, ki ∉ sobolevCutoffIndices N) (u : CriticalSobolev q) :
    criticalFiniteBandState q s (criticalCoeff q u) =
      criticalFiniteBandState q s (criticalCoeff q (u - criticalSobolevCutoff q N u)) := by
  apply WithLp.ext
  funext ki
  have hk : ki.val.1 ∉ sobolevCutoffModes N := by
    simpa only [sobolevCutoffIndices, Finset.mem_product, Finset.mem_univ, and_true] using
      hs ki.val ki.property
  change criticalWeightedCoeff q (criticalCoeff q u) ki.val =
    criticalWeightedCoeff q (criticalCoeff q (u - criticalSobolevCutoff q N u)) ki.val
  change _ = (criticalHalfWeight ki.val.1 : ℂ) ^ q *
    (criticalCoeff q u ki.val.1 ki.val.2 -
      criticalCoeff q (criticalSobolevCutoff q N u) ki.val.1 ki.val.2)
  rw [criticalSobolevCutoff_coeff, if_neg hk, sub_zero]
  rfl

theorem criticalFiniteBandState_tail_norm_le (q : ℤ) (s : Finset FourierIndex) (N : ℕ)
    (hs : ∀ ki ∈ s, ki ∉ sobolevCutoffIndices N) (u : CriticalSobolev q) :
    ‖criticalFiniteBandState q s (criticalCoeff q u)‖ ≤
      ‖u - criticalSobolevCutoff q N u‖ := by
  rw [criticalFiniteBandState_eq_tail q s N hs u]
  exact criticalFiniteBandState_norm_le q s _

theorem criticalFiniteBandState_norm_mono {q r : ℤ} (hqr : q ≤ r)
    (s : Finset FourierIndex) (c : FourierCoeff) :
    ‖criticalFiniteBandState q s c‖ ≤ ‖criticalFiniteBandState r s c‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  apply Finset.sum_le_sum
  intro ki _
  exact pow_le_pow_left₀ (norm_nonneg _) (criticalWeightedCoeff_norm_mono hqr c ki.val) 2

theorem criticalFiniteBandState_continuous (q : ℤ) (s : Finset FourierIndex) :
    Continuous (fun u : CriticalSobolev q =>
      criticalFiniteBandState q s (criticalCoeff q u)) := by
  apply PiLp.continuous_toLp.comp
  apply continuous_pi
  intro ki
  exact continuous_const.mul (criticalCoeff_continuous q ki.val.1 ki.val.2)

theorem criticalFiniteBandState_memLp
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (q : ℤ) (s : Finset FourierIndex) (u : α → CriticalSobolev q)
    (hu : MemLp u 2 μ) :
    MemLp (fun t => criticalFiniteBandState q s (criticalCoeff q (u t))) 2 μ := by
  apply hu.of_le ((criticalFiniteBandState_continuous q s).comp_aestronglyMeasurable
    hu.aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun t => criticalFiniteBandState_norm_le q s (u t)

/-- Every annulus beyond N is bounded in time L2 by the same-order full tail. -/
theorem criticalFiniteBandState_integral_tail_le
    (q : ℤ) (s : Finset FourierIndex) (N : ℕ)
    (hs : ∀ ki ∈ s, ki ∉ sobolevCutoffIndices N)
    (u : ℝ → CriticalSobolev q) {T : ℝ} (hT : 0 ≤ T)
    (hu : MemLp u 2 (volume.restrict (Icc (0 : ℝ) T))) :
    (∫ t in (0 : ℝ)..T, ‖criticalFiniteBandState q s (criticalCoeff q (u t))‖ ^ 2) ≤
      ∫ t in (0 : ℝ)..T, ‖u t - criticalSobolevCutoff q N (u t)‖ ^ 2 := by
  apply intervalIntegral.integral_mono_ae_restrict hT
  · exact (intervalIntegrable_iff_integrableOn_Icc_of_le hT).mpr
      (criticalTrace_integrable_norm_sq (criticalFiniteBandState_memLp q s u hu))
  · exact (intervalIntegrable_iff_integrableOn_Icc_of_le hT).mpr
      (criticalTrace_integrable_norm_sq (hu.sub ((criticalSobolevCutoff q N).comp_memLp' hu)))
  · exact Filter.Eventually.of_forall fun t =>
      pow_le_pow_left₀ (norm_nonneg _) (criticalFiniteBandState_tail_norm_le q s N hs (u t)) 2

end

end SingularClosure
