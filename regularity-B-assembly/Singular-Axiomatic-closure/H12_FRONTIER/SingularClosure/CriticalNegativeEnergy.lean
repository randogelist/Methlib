import SingularClosure.CriticalEnergy
import SingularClosure.CriticalSpacesCutoff
import SingularClosure.LerayL2Contraction

/-! Exact finite negative-half-order energies and the physical inverse-Lambda
pairing for the actual projected Galerkin transport. -/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory
open scoped BigOperators ContDiff

namespace SingularClosure

noncomputable section

def criticalNegativeEnergy (N : ℕ) (c : FourierCoeff) : ℝ :=
  ∑ k ∈ cutoffModes N, ∑ i : Fin 3,
    (criticalFrequencyWeight k)⁻¹ * Complex.normSq (c k i)

def criticalInverseLambdaCoefficient (c : FourierCoeff) : FourierCoeff :=
  fun k i => (((criticalFrequencyWeight k)⁻¹ : ℝ) : ℂ) * c k i

def criticalProjectedTransport (N : ℕ) (c : FourierCoeff) : FourierCoeff :=
  fun k => coefficientLeray k (coefficientTransport N c k)

theorem criticalNegativeEnergy_nonneg (N : ℕ) (c : FourierCoeff) :
    0 ≤ criticalNegativeEnergy N c := by
  apply Finset.sum_nonneg
  intro k _
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (inv_nonneg.mpr (criticalFrequencyWeight_pos k).le)
    (Complex.normSq_nonneg (c k i))

theorem criticalEnergy_one_inverseLambda (N : ℕ) (c : FourierCoeff) :
    criticalEnergy 1 N (criticalInverseLambdaCoefficient c) =
      criticalNegativeEnergy N c := by
  unfold criticalEnergy criticalNegativeEnergy
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro i _
  simp only [criticalInverseLambdaCoefficient, pow_one,
    Complex.normSq_mul, Complex.normSq_ofReal]
  field_simp [(criticalFrequencyWeight_pos k).ne'] <;> ring

theorem criticalFiniteSobolev_neg_one_norm_sq (N : ℕ) (c : FourierCoeff) :
    ‖criticalFiniteSobolev (-1) N c‖ ^ 2 = criticalNegativeEnergy N c := by
  simpa only [criticalNegativeEnergy, zpow_neg_one] using
    criticalFiniteSobolev_norm_sq (-1) N c

theorem criticalNegativeEnergy_laplacianCoefficient (N : ℕ) (c : FourierCoeff) :
    criticalNegativeEnergy N (laplacianCoefficient c) = criticalEnergy 3 N c := by
  unfold criticalNegativeEnergy criticalEnergy
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro i _
  simp only [laplacianCoefficient, Complex.normSq_mul,
    Complex.normSq_neg, Complex.normSq_ofReal]
  rw [← criticalFrequencyWeight_sq_of_cutoff hk]
  field_simp [(criticalFrequencyWeight_pos k).ne'] <;> ring

theorem criticalInverseLambdaCoefficient_reality (c : FourierCoeff)
    (hc : SpectralReality c) :
    SpectralReality (criticalInverseLambdaCoefficient c) := by
  intro k i
  simp [criticalInverseLambdaCoefficient, criticalFrequencyWeight_neg,
    hc k i, Complex.star_def]

theorem criticalProjectedTransport_solenoidal (N : ℕ) (c : FourierCoeff) :
    SpectralSolenoidal (criticalProjectedTransport N c) := by
  intro k
  exact coefficientLeray_solenoidal k (coefficientTransport N c k)

theorem criticalProjectedTransport_reality (N : ℕ) (c : FourierCoeff)
    (hc : SpectralReality c) :
    SpectralReality (criticalProjectedTransport N c) :=
  lerayFourierCoeff_reality (coefficientTransport N c)
    (coefficientTransport_reality N c hc)

/-- The literal inverse-Lambda test field pairs with the physical convection
to give the squared negative-half-order norm of its Leray projection. -/
theorem criticalInverseLambda_transport_pairing
    (N : ℕ) (c : FourierCoeff)
    (hsupp : ∀ k : Frequency, k ∉ cutoffModes N → ∀ i : Fin 3, c k i = 0)
    (hreal : SpectralReality c) :
    (∫ x in unitCube,
      inner ℝ (finiteSynthesis N
        (criticalInverseLambdaCoefficient (criticalProjectedTransport N c)) x)
        (convection (finiteSynthesis N c) x)) =
      criticalNegativeEnergy N (criticalProjectedTransport N c) := by
  rw [integral_finiteSynthesis_pairing N _ _
    (convection_continuous (finiteSynthesis_contDiff N c)),
    datumFourierCoeff_convection_finiteSynthesis N c hsupp hreal]
  unfold criticalNegativeEnergy
  apply Finset.sum_congr rfl
  intro k _
  have hnorm (z : ℂ) : (star z * z).re = Complex.normSq z := by
    simp only [Complex.star_def, Complex.mul_re,
      Complex.conj_re, Complex.conj_im, Complex.normSq_apply]
    ring
  have hpair := congrArg Complex.re
    (coefficientLeray_pairing k
      (coefficientLeray k (coefficientTransport N c k))
      (coefficientTransport N c k)
      (coefficientLeray_solenoidal k (coefficientTransport N c k)))
  have hsum :
      (∑ i : Fin 3,
        (star (criticalProjectedTransport N c k i) * coefficientTransport N c k i).re) =
      ∑ i : Fin 3, Complex.normSq (criticalProjectedTransport N c k i) := by
    simpa only [Complex.re_sum, hnorm, criticalProjectedTransport] using hpair.symm
  calc
    _ = (criticalFrequencyWeight k)⁻¹ *
        (∑ i : Fin 3,
          (star (criticalProjectedTransport N c k i) *
            coefficientTransport N c k i).re) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp only [criticalInverseLambdaCoefficient, Complex.star_def,
        Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
        Complex.ofReal_re, Complex.ofReal_im]
      ring
    _ = _ := by rw [hsum, Finset.mul_sum]

end

end SingularClosure
