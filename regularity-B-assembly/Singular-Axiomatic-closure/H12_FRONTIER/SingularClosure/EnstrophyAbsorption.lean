import SingularClosure.PeriodicNonlinear
import SingularClosure.PhysicalBilinear

/-!
# Cutoff-independent physical Galerkin enstrophy inequality

The proved physical Sobolev/Hölder estimate is converted to a finite real
constant, then absorbed by a fourth-power inequality. The final derivative
is that of the actual integral of the physical squared gradient, and the
dissipation is the actual squared L2 norm of the physical Laplacian.
-/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory
open scoped ContDiff ENNReal NNReal BigOperators RealInnerProductSpace

namespace SingularClosure

noncomputable section

theorem FINITE_PHYSICAL_NONLINEAR_REAL_BOUND :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, ∀ c : FourierCoeff, SpectralReality c →
      abs (∫ x in unitCube,
        inner ℝ (convection (finiteSynthesis N c) x) (laplacian (finiteSynthesis N c) x)) ≤
          K * (coefficientDissipation N c) ^ (3 / 4 : ℝ) *
            (coefficientLaplacianSquare N c) ^ (3 / 4 : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := FINITE_PHYSICAL_NONLINEAR_THREE_QUARTER_BOUND
  refine ⟨C.toReal, ENNReal.toReal_nonneg, ?_⟩
  intro N c hreal
  have h := ENNReal.toReal_mono (by finiteness) (hbound N c hreal)
  simpa only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal (abs_nonneg _),
    ENNReal.toReal_ofReal (coefficientDissipation_nonneg N c),
    ENNReal.toReal_ofReal (coefficientLaplacianSquare_nonneg N c)] using h

/-- Elementary fourth-power absorption, including the zero cases. -/
theorem quartic_absorption {x z d ν : ℝ} (hx : 0 ≤ x) (hz : 0 ≤ z)
    (hd : 0 ≤ d) (hν : 0 < ν) (hfour : x ^ 4 ≤ d * z ^ 3) :
    x ≤ ν * z + d / ν ^ 3 := by
  by_contra h
  have hlt : ν * z + d / ν ^ 3 < x := lt_of_not_ge h
  have hdz : 0 ≤ d / ν ^ 3 := div_nonneg hd (pow_nonneg hν.le _)
  have hnz : 0 ≤ ν * z := mul_nonneg hν.le hz
  have hnx : ν * z < x := lt_of_le_of_lt (le_add_of_nonneg_right hdz) hlt
  have hdx : d / ν ^ 3 < x := lt_of_le_of_lt (le_add_of_nonneg_left hnz) hlt
  have hxp : 0 < x := lt_of_le_of_lt hnz hnx
  have hcube : (ν * z) ^ 3 ≤ x ^ 3 := pow_le_pow_left₀ hnz hnx.le 3
  have hcontr : d * z ^ 3 < x ^ 4 := by
    calc
      _ = (ν * z) ^ 3 * (d / ν ^ 3) := by field_simp [ne_of_gt hν] <;> ring
      _ ≤ x ^ 3 * (d / ν ^ 3) := mul_le_mul_of_nonneg_right hcube hdz
      _ < x ^ 3 * x := mul_lt_mul_of_pos_left hdx (pow_pos hxp _)
      _ = _ := by ring
  exact (not_lt_of_ge hfour) hcontr

theorem real_three_quarter_pow_four (x : ℝ) (hx : 0 ≤ x) :
    (x ^ (3 / 4 : ℝ)) ^ (4 : ℕ) = x ^ (3 : ℕ) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

theorem nonlinear_three_quarter_absorption {K E Z ν : ℝ}
    (hK : 0 ≤ K) (hE : 0 ≤ E) (hZ : 0 ≤ Z) (hν : 0 < ν) :
    2 * K * E ^ (3 / 4 : ℝ) * Z ^ (3 / 4 : ℝ) ≤
      ν * Z + (2 * K) ^ 4 / ν ^ 3 * E ^ 3 := by
  have hpow : (2 * K * E ^ (3 / 4 : ℝ) * Z ^ (3 / 4 : ℝ)) ^ (4 : ℕ) =
      ((2 * K) ^ 4 * E ^ 3) * Z ^ 3 := by
    rw [mul_pow, mul_pow, real_three_quarter_pow_four E hE,
      real_three_quarter_pow_four Z hZ]
  have h := quartic_absorption
    (x := 2 * K * E ^ (3 / 4 : ℝ) * Z ^ (3 / 4 : ℝ))
    (z := Z) (d := (2 * K) ^ 4 * E ^ 3) (ν := ν)
    (by positivity) hZ (by positivity) hν hpow.le
  convert h using 1 <;> ring

theorem finite_laplacian_integral_norm_sq (N : ℕ) (c : FourierCoeff)
    (hreal : SpectralReality c) :
    (∫ x in unitCube, ‖laplacian (finiteSynthesis N c) x‖ ^ 2) =
      coefficientLaplacianSquare N c := by
  rw [finiteSynthesis_laplacian, ← physicalEnergy_eq_integral_norm_sq,
    FINITE_PHYSICAL_ENERGY_PARSEVAL N _ (laplacianCoefficient_reality c hreal),
    coefficientEnergy_laplacianCoefficient]

/-- A single constant controls the actual finite ODE enstrophy rates. -/
theorem GALERKIN_COEFFICIENT_ENSTROPHY_INEQUALITY :
    ∃ C : ℝ, 0 < C ∧ ∀ ν : ℝ, 0 < ν → ∀ a : Field, ∀ N : ℕ,
      ∀ g : GalerkinSolution ν a N, ∀ t : ℝ, 0 ≤ t → ∃ d : ℝ,
        HasDerivWithinAt (fun r => coefficientDissipation N (g.coeff r)) d (Ici 0) t ∧
          d + ν * coefficientLaplacianSquare N (g.coeff t) ≤
            C / ν ^ 3 * (coefficientDissipation N (g.coeff t)) ^ 3 := by
  obtain ⟨K, hK, hbound⟩ := FINITE_PHYSICAL_NONLINEAR_REAL_BOUND
  let C : ℝ := (2 * K) ^ 4 + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro ν hν a N g t ht
  refine ⟨(-2 * ν) * coefficientLaplacianSquare N (g.coeff t) -
    2 * coefficientEnstrophyNonlinearPower N (g.coeff t),
    g.coefficientEnstrophy_identity ht, ?_⟩
  have hE := coefficientDissipation_nonneg N (g.coeff t)
  have hZ := coefficientLaplacianSquare_nonneg N (g.coeff t)
  have hb := hbound N (g.coeff t) (g.real_symmetry t ht)
  have ha := nonlinear_three_quarter_absorption hK hE hZ hν
  have hNL : -2 * coefficientEnstrophyNonlinearPower N (g.coeff t) ≤
      ν * coefficientLaplacianSquare N (g.coeff t) +
        C / ν ^ 3 * (coefficientDissipation N (g.coeff t)) ^ 3 := by
    calc
      _ = 2 * (∫ x in unitCube,
          inner ℝ (convection (finiteSynthesis N (g.coeff t)) x)
            (laplacian (finiteSynthesis N (g.coeff t)) x)) := by
        rw [coefficientEnstrophyNonlinearPower_eq_physical N (g.coeff t)
          (g.mode_support t ht) (g.real_symmetry t ht) (g.solenoidal t ht)]
        ring
      _ ≤ 2 * abs (∫ x in unitCube,
          inner ℝ (convection (finiteSynthesis N (g.coeff t)) x)
            (laplacian (finiteSynthesis N (g.coeff t)) x)) := by
        exact mul_le_mul_of_nonneg_left (le_abs_self _) (by norm_num)
      _ ≤ 2 * (K * (coefficientDissipation N (g.coeff t)) ^ (3 / 4 : ℝ) *
          (coefficientLaplacianSquare N (g.coeff t)) ^ (3 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_left hb (by norm_num)
      _ = 2 * K * (coefficientDissipation N (g.coeff t)) ^ (3 / 4 : ℝ) *
          (coefficientLaplacianSquare N (g.coeff t)) ^ (3 / 4 : ℝ) := by ring
      _ ≤ ν * coefficientLaplacianSquare N (g.coeff t) +
          (2 * K) ^ 4 / ν ^ 3 * (coefficientDissipation N (g.coeff t)) ^ 3 := ha
      _ ≤ _ := by
        apply add_le_add (le_refl _)
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg hE _)
        apply div_le_div_of_nonneg_right _ (pow_nonneg hν.le _)
        dsimp [C]
        linarith
  nlinarith

/-- Frozen endpoint 5, stated using actual physical integrals and the actual
right derivative at zero. The universal constant is independent of N, ν and a. -/
theorem GALERKIN_ENSTROPHY_INEQUALITY :
    ∃ C : ℝ, 0 < C ∧ ∀ ν : ℝ, 0 < ν → ∀ a : Field, ∀ N : ℕ,
      ∀ g : GalerkinSolution ν a N, ∀ t : ℝ, 0 ≤ t → ∃ d : ℝ,
        HasDerivWithinAt
          (fun r => ∫ x in unitCube, gradientSquareDensity (g.velocity r) x)
          d (Ici 0) t ∧
        d + ν * (∫ x in unitCube, ‖laplacian (g.velocity t) x‖ ^ 2) ≤
          C / ν ^ 3 * (∫ x in unitCube, gradientSquareDensity (g.velocity t) x) ^ 3 := by
  obtain ⟨C, hC, hbound⟩ := GALERKIN_COEFFICIENT_ENSTROPHY_INEQUALITY
  refine ⟨C, hC, ?_⟩
  intro ν hν a N g t ht
  obtain ⟨d, hd, hineq⟩ := hbound ν hν a N g t ht
  have heq (r : ℝ) (hr : 0 ≤ r) :
      (∫ x in unitCube, gradientSquareDensity (g.velocity r) x) =
        coefficientDissipation N (g.coeff r) :=
    FINITE_PHYSICAL_REAL_ENSTROPHY_PARSEVAL N (g.coeff r) (g.real_symmetry r hr)
  refine ⟨d, hd.congr (fun r hr => heq r hr) (heq t ht), ?_⟩
  rw [heq t ht]
  change d + ν * (∫ x in unitCube,
    ‖laplacian (finiteSynthesis N (g.coeff t)) x‖ ^ 2) ≤ _
  rw [finite_laplacian_integral_norm_sq N (g.coeff t) (g.real_symmetry t ht)]
  exact hineq

end

end SingularClosure
