import SingularClosure.LerayL2Contraction
import SingularClosure.InitialCutoffBounds

/-!
# The literal Galerkin time derivative and its physical L² estimate

The time derivative is taken within the closed nonnegative half-line, so the
identification includes time zero. The nonlinear bound uses the actual
convection coefficients and the proved finite Bessel and Leray contractions.
-/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory
open scoped BigOperators ContDiff

namespace SingularClosure

noncomputable section

theorem finiteSynthesis_eq_sum_unitVector (N : ℕ) (c : FourierCoeff) (x : Vec) :
    finiteSynthesis N c x = ∑ i : Fin 3,
      (∑ k ∈ cutoffModes N, fourierCharacter k x * c k i).re • unitVector i := by
  ext j
  simp [finiteSynthesis, unitVector, EuclideanSpace.single_apply]

/-- Differentiation of the actual finite physical velocity, including the boundary. -/
theorem GalerkinSolution.velocity_hasDerivWithinAt
    {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N)
    (t : ℝ) (ht : 0 ≤ t) (x : Vec) :
    HasDerivWithinAt (fun s : ℝ => g.velocity s x)
      (finiteSynthesis N (galerkinRhs ν N (g.coeff t)) x) (Ici 0) t := by
  have hs (i : Fin 3) : HasDerivWithinAt
      (fun s : ℝ => ∑ k ∈ cutoffModes N, fourierCharacter k x * g.coeff s k i)
      (∑ k ∈ cutoffModes N, fourierCharacter k x * galerkinRhs ν N (g.coeff t) k i)
      (Ici 0) t := by
    apply HasDerivWithinAt.fun_sum
    intro k hk
    exact (g.equation t ht k hk i).const_mul (fourierCharacter k x)
  have hr (i : Fin 3) : HasDerivWithinAt
      (fun s : ℝ => (∑ k ∈ cutoffModes N, fourierCharacter k x * g.coeff s k i).re)
      (∑ k ∈ cutoffModes N,
        fourierCharacter k x * galerkinRhs ν N (g.coeff t) k i).re (Ici 0) t := by
    simpa only [Function.comp_def] using!
      Complex.reCLM.hasFDerivAt.comp_hasDerivWithinAt t (hs i)
  have hv : HasDerivWithinAt
      (fun s : ℝ => ∑ i : Fin 3,
        (∑ k ∈ cutoffModes N, fourierCharacter k x * g.coeff s k i).re • unitVector i)
      (∑ i : Fin 3, (∑ k ∈ cutoffModes N,
        fourierCharacter k x * galerkinRhs ν N (g.coeff t) k i).re • unitVector i)
      (Ici 0) t := by
    apply HasDerivWithinAt.fun_sum
    intro i _
    exact (hr i).smul_const (unitVector i)
  have hf : (fun s : ℝ => ∑ i : Fin 3,
      (∑ k ∈ cutoffModes N, fourierCharacter k x * g.coeff s k i).re • unitVector i) =
        (fun s : ℝ => g.velocity s x) := by
    funext s
    exact (finiteSynthesis_eq_sum_unitVector N (g.coeff s) x).symm
  rw [hf, ← finiteSynthesis_eq_sum_unitVector N (galerkinRhs ν N (g.coeff t)) x] at hv
  exact hv

theorem GalerkinSolution.timeDerivative_eq_finiteSynthesis
    {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N)
    (t : ℝ) (ht : 0 ≤ t) :
    timeDerivative g.velocity t = finiteSynthesis N (galerkinRhs ν N (g.coeff t)) := by
  funext x
  exact (g.velocity_hasDerivWithinAt t ht x).derivWithin ((uniqueDiffOn_Ici 0) t ht)

theorem complex_normSq_sub_le_twice (z w : ℂ) :
    Complex.normSq (z - w) ≤ 2 * Complex.normSq z + 2 * Complex.normSq w := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
  nlinarith [sq_nonneg (z.re + w.re), sq_nonneg (z.im + w.im)]

theorem normSq_viscous_coefficient (ν : ℝ) (k : Frequency) (z : ℂ) :
    Complex.normSq (-((ν * (2 * Real.pi) ^ 2 * (galerkinFreqSq k : ℝ) : ℝ) : ℂ) * z) =
      ν ^ 2 * (((2 * Real.pi) ^ 2 * (galerkinFreqSq k : ℝ)) ^ 2 * Complex.normSq z) := by
  simp only [Complex.normSq_mul, Complex.normSq_neg, Complex.normSq_ofReal]
  ring

theorem coefficientEnergy_galerkinRhs_le (ν : ℝ) (N : ℕ) (c : FourierCoeff) :
    coefficientEnergy N (galerkinRhs ν N c) ≤
      2 * ν ^ 2 * coefficientLaplacianSquare N c +
        2 * coefficientEnergy N (coefficientTransport N c) := by
  have hproj : coefficientEnergy N (galerkinRhs ν N c) ≤
      2 * ν ^ 2 * coefficientLaplacianSquare N c +
        2 * coefficientEnergy N (lerayFourierCoeff (coefficientTransport N c)) := by
    calc
      _ ≤ ∑ k ∈ cutoffModes N, ∑ i : Fin 3,
          (2 * ν ^ 2 * (((2 * Real.pi) ^ 2 * (galerkinFreqSq k : ℝ)) ^ 2 *
              Complex.normSq (c k i)) +
            2 * Complex.normSq (coefficientLeray k (coefficientTransport N c k) i)) := by
        apply Finset.sum_le_sum
        intro k _
        apply Finset.sum_le_sum
        intro i _
        calc
          _ ≤ 2 * Complex.normSq
              (-((ν * (2 * Real.pi) ^ 2 * (galerkinFreqSq k : ℝ) : ℝ) : ℂ) * c k i) +
              2 * Complex.normSq (coefficientLeray k (coefficientTransport N c k) i) :=
            complex_normSq_sub_le_twice _ _
          _ = _ := by rw [normSq_viscous_coefficient]; ring
      _ = _ := by
        simp only [coefficientLaplacianSquare, coefficientEnergy, lerayFourierCoeff,
          Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
  exact hproj.trans (add_le_add_left
    (mul_le_mul_of_nonneg_left
      (coefficientEnergy_leray_le N (coefficientTransport N c)) (by norm_num)) _)

theorem coefficientEnergy_transport_le_convection (N : ℕ) (c : FourierCoeff)
    (hsupp : ∀ k : Frequency, k ∉ cutoffModes N → ∀ i : Fin 3, c k i = 0)
    (hreal : SpectralReality c) :
    coefficientEnergy N (coefficientTransport N c) ≤
      physicalEnergy (convection (finiteSynthesis N c)) := by
  have h := coefficientEnergy_initial_cutoff_le N (convection (finiteSynthesis N c))
    (convection_continuous (finiteSynthesis_contDiff N c))
  rw [datumFourierCoeff_convection_finiteSynthesis N c hsupp hreal] at h
  exact h

/-- A literal physical time-derivative bound, with constants independent of the cutoff. -/
theorem GalerkinSolution.timeDerivative_L2_bound
    {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N)
    (t : ℝ) (ht : 0 ≤ t) :
    (∫ x in unitCube, ‖timeDerivative g.velocity t x‖ ^ 2) ≤
      2 * ν ^ 2 * coefficientLaplacianSquare N (g.coeff t) +
        2 * (∫ x in unitCube, ‖convection (g.velocity t) x‖ ^ 2) := by
  have hreal : SpectralReality (g.coeff t) := g.real_symmetry t ht
  have htrans := coefficientEnergy_transport_le_convection N (g.coeff t)
    (g.mode_support t ht) hreal
  have hrhs := coefficientEnergy_galerkinRhs_le ν N (g.coeff t)
  rw [g.timeDerivative_eq_finiteSynthesis t ht,
    ← physicalEnergy_eq_integral_norm_sq,
    FINITE_PHYSICAL_ENERGY_PARSEVAL N _ (galerkinRhs_reality ν N (g.coeff t) hreal)]
  have h := hrhs.trans (add_le_add_left
    (mul_le_mul_of_nonneg_left htrans (by norm_num : (0 : ℝ) ≤ 2)) _)
  simpa only [physicalEnergy_eq_integral_norm_sq, GalerkinSolution.velocity] using h

end

end SingularClosure
