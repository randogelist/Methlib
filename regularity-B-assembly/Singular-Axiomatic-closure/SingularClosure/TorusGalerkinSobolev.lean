import SingularClosure.TorusSobolev
import SingularClosure.EnstrophyAbsorption

/-!
# Actual Galerkin trajectories in the Fourier Sobolev spaces

Finite support proves membership in every integral Sobolev order. No membership
or norm-identification premise is assumed. The H¹ and H² squared norms are
exactly `E + D` and `E + 2D + Z`, with the actual unit-period derivative symbols.
For real coefficients, finite physical Parseval identifies all three terms
with the literal physical integrals. No compactness in time is asserted.
-/

set_option autoImplicit false

open Set MeasureTheory
open scoped BigOperators

namespace SingularClosure

noncomputable section

theorem torusSobolevWeight_sq (k : Frequency) :
    torusSobolevWeight k ^ 2 =
      1 + (2 * Real.pi) ^ 2 * (galerkinFreqSq k : ℝ) := by
  unfold torusSobolevWeight
  apply Real.sq_sqrt
  have hk : (0 : ℝ) ≤ (galerkinFreqSq k : ℝ) :=
    Int.cast_nonneg.mpr (galerkinFreqSq_nonneg k)
  positivity

/-- Every original Galerkin cutoff belongs to every Sobolev sequence space. -/
theorem cutoffCoeff_mem_torusSobolev (s N : ℕ) (c : FourierCoeff) :
    cutoffCoeff N c ∈ torusSobolevSubmodule s := by
  change Memℓp (sobolevWeightedCoeff s (cutoffCoeff N c)) 2
  apply Memℓp.of_exponent_ge (q := 0) _ (by norm_num)
  apply memℓp_zero
  apply ((cutoffModes N).product (Finset.univ : Finset (Fin 3))).finite_toSet.subset
  intro ki hki
  by_contra hnot
  have hk : ki.1 ∉ cutoffModes N := by simpa using hnot
  exact hki (by simp [sobolevWeightedCoeff, cutoffCoeff, hk])

/-- The original, nonzero-mode Fourier cutoff as an actual Sobolev vector. -/
def finiteSobolev (s N : ℕ) (c : FourierCoeff) : TorusSobolev s :=
  ⟨cutoffCoeff N c, cutoffCoeff_mem_torusSobolev s N c⟩

@[simp]
theorem finiteSobolev_coeff (s N : ℕ) (c : FourierCoeff) :
    (finiteSobolev s N c).val = cutoffCoeff N c := rfl

theorem finiteSobolev_norm_sq (s N : ℕ) (c : FourierCoeff) :
    ‖finiteSobolev s N c‖ ^ 2 =
      ∑ k ∈ cutoffModes N, ∑ i : Fin 3,
        (1 + (2 * Real.pi) ^ 2 * (galerkinFreqSq k : ℝ)) ^ s *
          Complex.normSq (c k i) := by
  rw [torusSobolev_norm_sq]
  let I : Finset FourierIndex := (cutoffModes N).product Finset.univ
  have htail : ∀ ki : FourierIndex, ki ∉ I →
      (torusSobolevWeight ki.1 ^ s *
        ‖(finiteSobolev s N c).val ki.1 ki.2‖) ^ 2 = 0 := by
    intro ki hki
    have hk : ki.1 ∉ cutoffModes N := by simpa [I] using hki
    simp [finiteSobolev_coeff, cutoffCoeff, hk]
  rw [tsum_eq_sum htail]
  dsimp [I]
  rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro i hi
  have hpow : (torusSobolevWeight k ^ s) ^ 2 =
      (torusSobolevWeight k ^ 2) ^ s := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm s 2]
  simp only [finiteSobolev_coeff, cutoffCoeff, if_pos hk, mul_pow,
    hpow, torusSobolevWeight_sq, Complex.normSq_eq_norm_sq]

theorem finiteSobolev_H1_norm_sq (N : ℕ) (c : FourierCoeff) :
    ‖finiteSobolev 1 N c‖ ^ 2 = coefficientEnergy N c + coefficientDissipation N c := by
  rw [finiteSobolev_norm_sq]
  simp only [pow_one, add_mul, one_mul, Finset.sum_add_distrib,
    coefficientEnergy, coefficientDissipation]

theorem finiteSobolev_H2_norm_sq (N : ℕ) (c : FourierCoeff) :
    ‖finiteSobolev 2 N c‖ ^ 2 = coefficientEnergy N c +
      2 * coefficientDissipation N c + coefficientLaplacianSquare N c := by
  rw [finiteSobolev_norm_sq]
  have hterm (k : Frequency) (i : Fin 3) :
      (1 + (2 * Real.pi) ^ 2 * (galerkinFreqSq k : ℝ)) ^ 2 * Complex.normSq (c k i) =
        Complex.normSq (c k i) +
          2 * ((2 * Real.pi) ^ 2 * (galerkinFreqSq k : ℝ) * Complex.normSq (c k i)) +
          ((2 * Real.pi) ^ 2 * (galerkinFreqSq k : ℝ)) ^ 2 * Complex.normSq (c k i) := by
    ring
  simp only [hterm, coefficientEnergy, coefficientDissipation,
    coefficientLaplacianSquare, Finset.sum_add_distrib, Finset.mul_sum]

theorem finiteSobolev_H1_physical_norm_sq (N : ℕ) (c : FourierCoeff)
    (hreal : SpectralReality c) :
    ‖finiteSobolev 1 N c‖ ^ 2 =
      (∫ x in unitCube, ‖finiteSynthesis N c x‖ ^ 2) +
        ∫ x in unitCube, gradientSquareDensity (finiteSynthesis N c) x := by
  rw [finiteSobolev_H1_norm_sq,
    ← FINITE_PHYSICAL_ENERGY_PARSEVAL N c hreal,
    ← FINITE_PHYSICAL_REAL_ENSTROPHY_PARSEVAL N c hreal,
    physicalEnergy_eq_integral_norm_sq]

theorem finiteSobolev_H2_physical_norm_sq (N : ℕ) (c : FourierCoeff)
    (hreal : SpectralReality c) :
    ‖finiteSobolev 2 N c‖ ^ 2 =
      (∫ x in unitCube, ‖finiteSynthesis N c x‖ ^ 2) +
        2 * (∫ x in unitCube, gradientSquareDensity (finiteSynthesis N c) x) +
        ∫ x in unitCube, ‖laplacian (finiteSynthesis N c) x‖ ^ 2 := by
  rw [finiteSobolev_H2_norm_sq,
    ← FINITE_PHYSICAL_ENERGY_PARSEVAL N c hreal,
    ← FINITE_PHYSICAL_REAL_ENSTROPHY_PARSEVAL N c hreal,
    ← finite_laplacian_integral_norm_sq N c hreal,
    physicalEnergy_eq_integral_norm_sq]

/-- The actual Fourier-Galerkin trajectory in every integral Sobolev order. -/
def GalerkinSolution.sobolevState {ν : ℝ} {a : Field} {N : ℕ}
    (g : GalerkinSolution ν a N) (s : ℕ) (t : ℝ) : TorusSobolev s :=
  finiteSobolev s N (g.coeff t)

theorem GalerkinSolution.sobolevState_coeff {ν : ℝ} {a : Field} {N : ℕ}
    (g : GalerkinSolution ν a N) (s : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    (g.sobolevState s t).val = g.coeff t :=
  g.cutoffCoeff_eq t ht

theorem GalerkinSolution.sobolevState_inclusion {ν : ℝ} {a : Field} {N : ℕ}
    (g : GalerkinSolution ν a N) (s : ℕ) (t : ℝ) :
    torusSobolevInclusion s (g.sobolevState (s + 1) t) = g.sobolevState s t := by
  apply Subtype.ext
  rfl

theorem GalerkinSolution.sobolevState_H1_physical_norm_sq
    {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖g.sobolevState 1 t‖ ^ 2 =
      (∫ x in unitCube, ‖g.velocity t x‖ ^ 2) +
        ∫ x in unitCube, gradientSquareDensity (g.velocity t) x :=
  finiteSobolev_H1_physical_norm_sq N (g.coeff t) (g.real_symmetry t ht)

theorem GalerkinSolution.sobolevState_H2_physical_norm_sq
    {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖g.sobolevState 2 t‖ ^ 2 =
      (∫ x in unitCube, ‖g.velocity t x‖ ^ 2) +
        2 * (∫ x in unitCube, gradientSquareDensity (g.velocity t) x) +
        ∫ x in unitCube, ‖laplacian (g.velocity t) x‖ ^ 2 :=
  finiteSobolev_H2_physical_norm_sq N (g.coeff t) (g.real_symmetry t ht)

end

end SingularClosure
