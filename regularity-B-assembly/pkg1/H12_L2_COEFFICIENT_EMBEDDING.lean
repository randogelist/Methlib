import H12_SIGMA_ZERO_SMALL_CLASS

/-!
# Critical coefficient data embed in square-summable coefficients

The zero Fourier mode is excluded by the datum contract.  Every remaining
integer mode has physical frequency at least `2 * Real.pi`.  This gives the
exact coefficient estimate `sum ||a_k||² <= criticalSq a / (2*pi)`.

All objects here are the concrete coefficients of `RealH12Datum`.  This file
does not assert physical Fourier synthesis or a Navier--Stokes evolution.
-/

set_option autoImplicit false

open scoped BigOperators

noncomputable section

namespace H12L2CoefficientEmbedding

open H12FourierFoundations H12SpectralEnergyBridge H12SigmaZeroSmallClass

/-- A nonzero integer Fourier vector has Euclidean norm at least one. -/
theorem one_le_modeReal_norm {k : Mode3} (hk : k ≠ 0) :
    1 ≤ ‖modeReal k‖ := by
  classical
  have hex : ∃ i : Fin 3, k i ≠ 0 := by
    by_contra! h
    apply hk
    funext i
    exact h i
  obtain ⟨i, hi⟩ := hex
  have hcoord : (1 : ℝ) ≤ |(k i : ℝ)| := by
    have hcases : k i ≤ -1 ∨ 1 ≤ k i := by omega
    rcases hcases with hneg | hpos
    · have hn : (k i : ℝ) ≤ -1 := by exact_mod_cast hneg
      have ha := neg_le_abs (k i : ℝ)
      linarith
    · have hp : (1 : ℝ) ≤ (k i : ℝ) := by exact_mod_cast hpos
      exact hp.trans (le_abs_self _)
  have hcomponent : |(k i : ℝ)| ≤ ‖modeReal k‖ := by
    simpa [modeReal, Real.norm_eq_abs] using
      (PiLp.norm_apply_le (modeReal k) i)
  exact hcoord.trans hcomponent

/-- The exact physical spectral gap on the unit torus. -/
theorem physical_frequency_gap {k : Mode3} (hk : k ≠ 0) :
    2 * Real.pi ≤ freq k := by
  have hπ : 0 ≤ 2 * Real.pi := by positivity
  calc
    2 * Real.pi = (2 * Real.pi) * 1 := by ring
    _ ≤ (2 * Real.pi) * ‖modeReal k‖ :=
      mul_le_mul_of_nonneg_left (one_le_modeReal_norm hk) hπ
    _ = freq k := rfl

theorem physical_frequency_pos {k : Mode3} (hk : k ≠ 0) :
    0 < freq k := by
  exact (by positivity : (0 : ℝ) < 2 * Real.pi).trans_le
    (physical_frequency_gap hk)

/-- Mean-zero data obey the spectral-gap estimate at every Fourier mode. -/
theorem coefficient_square_mul_gap_le (a : RealH12Datum) (k : Mode3) :
    (2 * Real.pi) * ‖a.coeff k‖ ^ 2 ≤ hhalfTerm a.coeff k := by
  by_cases hk : k = 0
  · subst k
    simp [hhalfTerm, a.meanZero]
  · exact mul_le_mul_of_nonneg_right
      (physical_frequency_gap hk) (sq_nonneg ‖a.coeff k‖)

theorem coefficient_square_le_critical_density (a : RealH12Datum) (k : Mode3) :
    ‖a.coeff k‖ ^ 2 ≤ hhalfTerm a.coeff k / (2 * Real.pi) := by
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  apply (le_div_iff₀ hπ).2
  simpa only [mul_comm] using coefficient_square_mul_gap_le a k

/-- The critical coefficient carrier has a genuine finite L² coefficient sum. -/
theorem coefficient_l2_summable (a : RealH12Datum) :
    Summable (fun k : Mode3 => ‖a.coeff k‖ ^ 2) := by
  exact Summable.of_nonneg_of_le
    (fun k => sq_nonneg ‖a.coeff k‖)
    (fun k => coefficient_square_le_critical_density a k)
    (a.hhalfSummable.div_const (2 * Real.pi))

/-- Squared L² coefficient norm; physical synthesis is not asserted here. -/
def coefficientL2Sq (a : RealH12Datum) : ℝ :=
  ∑' k : Mode3, ‖a.coeff k‖ ^ 2

theorem coefficientL2Sq_nonneg (a : RealH12Datum) :
    0 ≤ coefficientL2Sq a := by
  exact tsum_nonneg (fun k => sq_nonneg ‖a.coeff k‖)

/-- Exact spectral-gap embedding constant for the unit torus. -/
theorem coefficientL2Sq_le_criticalSq (a : RealH12Datum) :
    coefficientL2Sq a ≤ criticalSq a / (2 * Real.pi) := by
  calc
    coefficientL2Sq a ≤
        ∑' k : Mode3, hhalfTerm a.coeff k / (2 * Real.pi) :=
      (coefficient_l2_summable a).tsum_le_tsum
        (fun k => coefficient_square_le_critical_density a k)
        (a.hhalfSummable.div_const (2 * Real.pi))
    _ = criticalSq a / (2 * Real.pi) := by
      rw [tsum_div_const]
      rfl

/-- Each coefficient square is bounded by the actual convergent coefficient sum. -/
theorem coefficient_square_le_l2Sq (a : RealH12Datum) (k : Mode3) :
    ‖a.coeff k‖ ^ 2 ≤ coefficientL2Sq a := by
  classical
  have h := Summable.sum_le_tsum ({k} : Finset Mode3)
    (fun j _ => sq_nonneg ‖a.coeff j‖) (coefficient_l2_summable a)
  simpa only [Finset.sum_singleton, coefficientL2Sq] using h

/-- The homogeneous critical quantity is definite on mean-zero coefficients. -/
theorem criticalSq_eq_zero_iff (a : RealH12Datum) :
    criticalSq a = 0 ↔ ∀ k : Mode3, a.coeff k = 0 := by
  constructor
  · intro ha k
    have hl2 : coefficientL2Sq a ≤ 0 := by
      simpa only [ha, zero_div] using coefficientL2Sq_le_criticalSq a
    have hk : ‖a.coeff k‖ ^ 2 ≤ 0 :=
      (coefficient_square_le_l2Sq a k).trans hl2
    have hn : ‖a.coeff k‖ = 0 := by
      nlinarith [norm_nonneg (a.coeff k)]
    exact norm_eq_zero.mp hn
  · intro ha
    simp [criticalSq, hhalfSq, hhalfTerm, ha]

theorem criticalNorm_eq_zero_iff (a : RealH12Datum) :
    criticalNorm a = 0 ↔ ∀ k : Mode3, a.coeff k = 0 := by
  constructor
  · intro ha
    apply (criticalSq_eq_zero_iff a).1
    rw [← criticalNorm_sq a, ha]
    norm_num
  · intro ha
    unfold criticalNorm
    rw [(criticalSq_eq_zero_iff a).2 ha]
    exact Real.sqrt_zero

/-- Concrete endpoint: summability, quantitative embedding, and definiteness. -/
theorem H12_L2_COEFFICIENT_EMBEDDING (a : RealH12Datum) :
    Summable (fun k : Mode3 => ‖a.coeff k‖ ^ 2) ∧
      coefficientL2Sq a ≤ criticalSq a / (2 * Real.pi) ∧
      (criticalSq a = 0 ↔ ∀ k : Mode3, a.coeff k = 0) := by
  exact ⟨coefficient_l2_summable a, coefficientL2Sq_le_criticalSq a,
    criticalSq_eq_zero_iff a⟩

end H12L2CoefficientEmbedding
