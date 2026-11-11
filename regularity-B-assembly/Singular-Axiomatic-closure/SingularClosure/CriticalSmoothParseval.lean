import SingularClosure.CriticalSpaces
import SingularClosure.FourierProduct
import SingularClosure.PhysicalEnergy

/-! Infinite physical cube Parseval for smooth real Fourier synthesis.

The scalar identity is obtained from the actual physical product coefficient
at frequency zero. Summability of the derivative energies follows from the
concrete half-order Hilbert representation, and all exchanges of sums are
justified before the homogeneous H1 norm is identified.
-/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

namespace SingularClosure

noncomputable section

theorem critical_smoothFourierSynthesis_component_parseval
    (c : FourierCoeff) (hc : ∀ i : Fin 3, RapidScalarFourier (fun k => c k i))
    (hreal : SpectralReality c) (i : Fin 3) :
    (∫ x in unitCube, (smoothFourierSynthesis c x i) ^ 2) =
      ∑' k : Frequency, Complex.normSq (c k i) := by
  have h := scalarFourierSeries_product_coefficient
    (fun k => c k i) (fun k => c k i) (hc i).summable_norm (hc i).summable_norm 0
  have hchar (x : Vec) : fourierCharacter 0 x = 1 := by
    simp [fourierCharacter]
  have hpair (k : Frequency) : c k i * c (0 - k) i = (Complex.normSq (c k i) : ℂ) := by
    rw [zero_sub, hreal, mul_comm]
    exact (Complex.normSq_eq_conj_mul_self (z := c k i)).symm
  simp_rw [hchar, star_one, one_mul,
    scalarFourierSeries_eq_smoothFourierSynthesis_component c hreal, hpair] at h
  rw [← Complex.ofReal_tsum] at h
  have hcast : (fun x : Vec =>
      (smoothFourierSynthesis c x i : ℂ) * (smoothFourierSynthesis c x i : ℂ)) =
      (fun x : Vec => (((smoothFourierSynthesis c x i) ^ 2 : ℝ) : ℂ)) := by
    funext x
    simp only [Complex.ofReal_pow, pow_two, Complex.ofReal_mul]
  rw [hcast, integral_complex_ofReal] at h
  exact Complex.ofReal_injective h

theorem critical_sum_derivative_normSq (c : FourierCoeff) (k : Frequency) (i : Fin 3) :
    (∑ j : Fin 3, Complex.normSq (spectralMultiplier (derivativeSymbol j) c k i)) =
      laplacianFrequency k * Complex.normSq (c k i) := by
  simp_rw [normSq_derivativeMultiplier]
  rw [← Finset.sum_mul, sum_derivativeScale_sq]

theorem critical_weight_two_laplacian (c : FourierCoeff) (hzero : SpectralMeanZero c)
    (k : Frequency) (i : Fin 3) :
    criticalFrequencyWeight k ^ (2 : ℤ) * Complex.normSq (c k i) =
      laplacianFrequency k * Complex.normSq (c k i) := by
  by_cases hk : k = 0
  · subst k
    simp only [hzero i, Complex.normSq_zero, mul_zero]
  · simp only [zpow_ofNat, criticalFrequencyWeight_sq_of_ne_zero k hk]

theorem critical_H1_laplacian_summable (w : CriticalSobolev 2)
    (hzero : SpectralMeanZero (criticalCoeff 2 w)) :
    Summable (fun ki : FourierIndex =>
      laplacianFrequency ki.1 * Complex.normSq (criticalCoeff 2 w ki.1 ki.2)) := by
  have hs : Summable (fun ki : FourierIndex =>
      ‖criticalWeightedCoeff 2 (criticalCoeff 2 w) ki‖ ^ 2) := by
    have h := (criticalCoeff_mem 2 w).summable
      (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h
  have heq (ki : FourierIndex) :
      ‖criticalWeightedCoeff 2 (criticalCoeff 2 w) ki‖ ^ 2 =
        laplacianFrequency ki.1 * Complex.normSq (criticalCoeff 2 w ki.1 ki.2) := by
    rw [criticalWeightedCoeff_norm, mul_pow, criticalHalfWeight_zpow_sq,
      ← Complex.normSq_eq_norm_sq, critical_weight_two_laplacian _ hzero]
  simpa only [heq] using hs

set_option maxHeartbeats 800000 in
/-- Literal physical dissipation equals the actual homogeneous H1 Hilbert norm. -/
theorem critical_smoothFourierSynthesis_dissipation_eq_norm_sq
    (c : FourierCoeff) (hc : ∀ i : Fin 3, RapidScalarFourier (fun k => c k i))
    (hreal : SpectralReality c) (hzero : SpectralMeanZero c)
    (w : CriticalSobolev 2) (hw : criticalCoeff 2 w = c) :
    physicalDissipation (smoothFourierSynthesis c) = ‖w‖ ^ 2 := by
  have hsum : Summable (fun ki : FourierIndex =>
      laplacianFrequency ki.1 * Complex.normSq (c ki.1 ki.2)) := by
    simpa only [hw] using critical_H1_laplacian_summable w (by simpa only [hw] using hzero)
  have hcomponent (i : Fin 3) : Summable (fun k : Frequency =>
      laplacianFrequency k * Complex.normSq (c k i)) :=
    hsum.comp_injective (i := fun k : Frequency => (k, i))
      (fun k l h => congrArg Prod.fst h)
  have hd (j i : Fin 3) : Summable (fun k : Frequency =>
      Complex.normSq (spectralMultiplier (derivativeSymbol j) c k i)) := by
    apply Summable.of_nonneg_of_le (fun k => Complex.normSq_nonneg _) _ (hcomponent i)
    intro k
    rw [← critical_sum_derivative_normSq c k i]
    exact Finset.single_le_sum (fun l _ => Complex.normSq_nonneg _)
      (Finset.mem_univ j)
  have hrapid (j i : Fin 3) :
      RapidScalarFourier (fun k => spectralMultiplier (derivativeSymbol j) c k i) := by
    simpa only [fourierPhaseCLM_unitVector, spectralMultiplier] using
      (hc i).directional (unitVector j)
  calc
    _ = ∑ j : Fin 3, ∑ i : Fin 3,
        ∫ x in unitCube, (coordinateDerivative (smoothFourierSynthesis c) j x i) ^ 2 :=
      integral_gradientSquareDensity (smoothFourierSynthesis_contDiff c hc)
    _ = ∑ j : Fin 3, ∑ i : Fin 3, ∑' k : Frequency,
        Complex.normSq (spectralMultiplier (derivativeSymbol j) c k i) := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      rw [smoothFourierSynthesis_coordinateDerivative c hc j]
      exact critical_smoothFourierSynthesis_component_parseval _ (hrapid j)
        (derivativeMultiplier_reality c hreal j) i
    _ = ∑ i : Fin 3, ∑ j : Fin 3, ∑' k : Frequency,
        Complex.normSq (spectralMultiplier (derivativeSymbol j) c k i) := Finset.sum_comm
    _ = ∑ i : Fin 3, ∑' k : Frequency,
        laplacianFrequency k * Complex.normSq (c k i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← Summable.tsum_finsetSum (fun j _ => hd j i)]
      exact tsum_congr (fun k => critical_sum_derivative_normSq c k i)
    _ = ∑' k : Frequency, ∑ i : Fin 3,
        laplacianFrequency k * Complex.normSq (c k i) :=
      (Summable.tsum_finsetSum (fun i _ => hcomponent i)).symm
    _ = ∑' ki : FourierIndex,
        laplacianFrequency ki.1 * Complex.normSq (c ki.1 ki.2) := by
      simpa only [tsum_fintype] using hsum.tsum_prod.symm
    _ = ‖w‖ ^ 2 := by
      rw [criticalSobolev_norm_sq, hw]
      exact tsum_congr (fun ki => (critical_weight_two_laplacian c hzero ki.1 ki.2).symm)

end

end SingularClosure
