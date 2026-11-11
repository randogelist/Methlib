import SingularClosure.Ax6ExactBudget
import SingularClosure.EnstrophyAbsorption
import SingularClosure.InitialCutoffBounds
import SingularClosure.GalerkinExistence
import SingularClosure.CubicBudget

/-!
# Concrete uniform enstrophy and accumulated Laplacian bounds

All analytic inputs are the actual Galerkin equation and AX6. The initial
bound is proved by physical Fourier cutoff contraction. This module is the
spatial-bound part of endpoint 7; it does not claim the time-derivative bound.
-/

set_option autoImplicit false

open Set MeasureTheory
open scoped BigOperators Interval

namespace SingularClosure

noncomputable section

def coefficientEnstrophyRate (ν : ℝ) (N : ℕ) (c : FourierCoeff) : ℝ :=
  ∑ k ∈ cutoffModes N, ∑ i : Fin 3,
    ((2 * Real.pi) ^ 2 * (galerkinFreqSq k : ℝ)) *
      (2 * (star (c k i) * galerkinRhs ν N c k i).re)

theorem GalerkinSolution.rhs_continuousOn
    {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N)
    {k : Frequency} (hk : k ∈ cutoffModes N) (i : Fin 3) :
    ContinuousOn (fun t => galerkinRhs ν N (g.coeff t) k i) (Ici 0) := by
  have h := (contDiff_finiteGalerkinRhs ν N).continuous.comp_continuousOn
    g.finite_continuousOn
  have hc := continuousOn_pi.1 (continuousOn_pi.1 h ⟨k, hk⟩) i
  apply hc.congr
  intro t ht
  simp only [finiteGalerkinRhs, extend_restrictFiniteState,
    g.cutoffCoeff_eq t ht]

theorem GalerkinSolution.coefficientEnstrophyRate_continuousOn
    {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N) :
    ContinuousOn (fun t => coefficientEnstrophyRate ν N (g.coeff t)) (Ici 0) := by
  unfold coefficientEnstrophyRate
  apply continuousOn_finset_sum
  intro k hk
  apply continuousOn_finset_sum
  intro i hi
  apply continuousOn_const.mul
  apply continuousOn_const.mul
  exact Complex.continuous_re.comp_continuousOn
    ((g.coefficient_continuous k i).star.mul (g.rhs_continuousOn hk i))

theorem GalerkinSolution.coefficientLaplacianSquare_continuousOn
    {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N) :
    ContinuousOn (fun t => coefficientLaplacianSquare N (g.coeff t)) (Ici 0) := by
  unfold coefficientLaplacianSquare
  apply continuousOn_finset_sum
  intro k hk
  apply continuousOn_finset_sum
  intro i hi
  simp_rw [Complex.normSq_eq_norm_sq]
  exact continuousOn_const.mul ((g.coefficient_continuous k i).norm.pow 2)

theorem AX6_UNIFORM_ENSTROPHY_ACCUMULATION (hAX6 : AX6Statement)
    (ν : ℝ) (hν : 0 < ν) (a : Field) (ha : SmoothSigmaZero a)
    (T : ℝ) (hT : 0 < T) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ, 1 ≤ N → ∀ g : GalerkinSolution ν a N,
      ∀ t ∈ Icc (0 : ℝ) T,
        coefficientDissipation N (g.coeff t) +
          ν * (∫ s in (0 : ℝ)..t, coefficientLaplacianSquare N (g.coeff s)) ≤ B := by
  obtain ⟨C, hC, hineq⟩ := GALERKIN_COEFFICIENT_ENSTROPHY_INEQUALITY
  obtain ⟨M, hM, hbudget⟩ := AX6_EXACT_REAL_SQUARE_BUDGET hAX6 ν hν a ha T hT
  let E₀ : ℝ := ∫ x in unitCube, gradientSquareDensity a x
  let κ : ℝ := C / ν ^ 3
  have hE₀ : 0 ≤ E₀ := integral_nonneg (gradientSquareDensity_nonneg a)
  have hκ : 0 ≤ κ := div_nonneg hC.le (pow_nonneg hν.le _)
  refine ⟨E₀ * Real.exp (κ * M), mul_nonneg hE₀ (Real.exp_pos _).le, ?_⟩
  intro N hN g
  let y := fun t => coefficientDissipation N (g.coeff t)
  let z := fun t => Real.sqrt (coefficientLaplacianSquare N (g.coeff t))
  let d := fun t => coefficientEnstrophyRate ν N (g.coeff t)
  have hy : ContinuousOn y (Icc 0 T) :=
    g.coefficientDissipation_continuousOn.mono (fun t ht => ht.1)
  have hz : ContinuousOn z (Icc 0 T) :=
    (Real.continuous_sqrt.comp_continuousOn
      g.coefficientLaplacianSquare_continuousOn).mono (fun t ht => ht.1)
  have hd : ContinuousOn d (Icc 0 T) :=
    g.coefficientEnstrophyRate_continuousOn.mono (fun t ht => ht.1)
  have hderiv : ∀ t ∈ Ioo (0 : ℝ) T, HasDerivAt y (d t) t := by
    intro t ht
    exact (g.coefficientDissipation_hasDerivWithinAt ht.1.le).hasDerivAt
      (Ici_mem_nhds ht.1)
  have hcubic : ∀ t ∈ Ioo (0 : ℝ) T,
      d t + ν * (z t) ^ 2 ≤ κ * (y t) ^ 3 := by
    intro t ht
    obtain ⟨d', hd', hbound⟩ := hineq ν hν a N g t ht.1.le
    have heq : d t = d' := (hderiv t ht).unique
      (hd'.hasDerivAt (Ici_mem_nhds ht.1))
    dsimp only [z]
    rw [Real.sq_sqrt (coefficientLaplacianSquare_nonneg N (g.coeff t)), heq]
    exact hbound
  have h := CUBIC_ENERGY_OF_SQUARE_BUDGET hν hκ hT.le hM hy hz hd
    (fun t _ => coefficientDissipation_nonneg N (g.coeff t))
    (g.coefficientDissipation_initial_le ha) hderiv hcubic (hbudget N hN g).2
  intro t ht
  have hzsq (s : ℝ) : (z s) ^ 2 = coefficientLaplacianSquare N (g.coeff s) :=
    Real.sq_sqrt (coefficientLaplacianSquare_nonneg N (g.coeff s))
  simpa only [hzsq] using h t ht

theorem AX6_UNIFORM_PHYSICAL_ENSTROPHY_ACCUMULATION (hAX6 : AX6Statement)
    (ν : ℝ) (hν : 0 < ν) (a : Field) (ha : SmoothSigmaZero a)
    (T : ℝ) (hT : 0 < T) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ, 1 ≤ N → ∀ g : GalerkinSolution ν a N,
      ∀ t ∈ Icc (0 : ℝ) T,
        (∫ x in unitCube, gradientSquareDensity (g.velocity t) x) +
          ν * (∫ s in (0 : ℝ)..t,
            ∫ x in unitCube, ‖laplacian (g.velocity s) x‖ ^ 2) ≤ B := by
  obtain ⟨B, hB, hb⟩ := AX6_UNIFORM_ENSTROPHY_ACCUMULATION hAX6 ν hν a ha T hT
  refine ⟨B, hB, ?_⟩
  intro N hN g t ht
  have he := FINITE_PHYSICAL_REAL_ENSTROPHY_PARSEVAL N (g.coeff t)
    (g.real_symmetry t ht.1)
  have hZ : (∫ s in (0 : ℝ)..t,
      ∫ x in unitCube, ‖laplacian (g.velocity s) x‖ ^ 2) =
      ∫ s in (0 : ℝ)..t, coefficientLaplacianSquare N (g.coeff s) := by
    apply intervalIntegral.integral_congr
    intro s hs
    have hs' : s ∈ Icc (0 : ℝ) t := by simpa only [uIcc_of_le ht.1] using hs
    exact finite_laplacian_integral_norm_sq N (g.coeff s) (g.real_symmetry s hs'.1)
  rw [he, hZ]
  exact hb N hN g t ht

end

end SingularClosure
