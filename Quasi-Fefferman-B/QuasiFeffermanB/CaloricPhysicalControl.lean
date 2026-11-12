import QuasiFeffermanB.CaloricMultiplier
import QuasiFeffermanB.CaloricEnstrophy
import SingularClosure.CriticalCubeL2
import SingularClosure.EnstrophyAbsorption

/-! Exact physical enstrophy control by the Euclidean Fourier ell1 norm. -/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal Topology Interval

namespace QuasiFeffermanB
open SingularClosure
noncomputable section

theorem caloric_fourierCharacter_norm (k : Frequency) (x : Vec) :
    ‖fourierCharacter k x‖ = 1 := fourierCharacter_norm k x

/-- The modulus is the Euclidean complex coefficient modulus. -/
theorem FINITE_SYNTHESIS_NORM_LE_CHI0
    (N : ℕ) (c : FourierCoeff) (x : Vec) :
    ‖finiteSynthesis N c x‖ ≤ finiteChi0 (cutoffModes N) c := by
  classical
  let F : Frequency → Vec := fun k =>
    WithLp.toLp 2 (fun i : Fin 3 => (fourierCharacter k x * c k i).re)
  have hsum : finiteSynthesis N c x = ∑ k ∈ cutoffModes N, F k := by
    ext i
    change (∑ k ∈ cutoffModes N, fourierCharacter k x * c k i).re =
      (EuclideanSpace.proj i : Vec →L[ℝ] ℝ) (∑ k ∈ cutoffModes N, F k)
    rw [map_sum]
    simp only [physical_complex_re_sum, F, EuclideanSpace.coe_proj]
  have hmode (k : Frequency) : ‖F k‖ ≤ complexVecNorm (c k) := by
    apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [EuclideanSpace.real_norm_sq_eq]
    change (∑ i : Fin 3, (fourierCharacter k x * c k i).re ^ 2) ≤
      (Real.sqrt (∑ i : Fin 3, ‖c k i‖ ^ 2)) ^ 2
    rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
    apply Finset.sum_le_sum
    intro i _
    calc
      _ = |(fourierCharacter k x * c k i).re| ^ 2 := (sq_abs _).symm
      _ ≤ ‖fourierCharacter k x * c k i‖ ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_re_le_norm _) 2
      _ = ‖c k i‖ ^ 2 := by rw [norm_mul, caloric_fourierCharacter_norm, one_mul]
  rw [hsum]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun k _ => hmode k))

/-- Sharp finite-dimensional Cauchy-Schwarz for the literal convection.
The gradient density is the Hilbert-Schmidt square, so the constant is one. -/
theorem CONVECTION_NORM_SQ_LE_GRADIENT_DENSITY (v : Field) (x : Vec) :
    ‖convection v x‖ ^ 2 ≤ ‖v x‖ ^ 2 * gradientSquareDensity v x := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp_rw [convection_component_eq_sum]
  calc
    _ ≤ ∑ i : Fin 3, (∑ j : Fin 3, v x j ^ 2) *
        ∑ j : Fin 3, coordinateDerivative v j x i ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
        (fun j : Fin 3 => v x j) (fun j : Fin 3 => coordinateDerivative v j x i)
    _ = ‖v x‖ ^ 2 * gradientSquareDensity v x := by
      rw [← Finset.mul_sum, EuclideanSpace.real_norm_sq_eq]
      unfold gradientSquareDensity
      congr 1
      exact Finset.sum_comm

theorem PHYSICAL_PAIRING_SQUARE_LE_ENERGY_PRODUCT
    (v w : Field) (hv : Continuous v) (hw : Continuous w) :
    (∫ x in unitCube, inner ℝ (v x) (w x)) ^ 2 ≤
      physicalEnergy v * physicalEnergy w := by
  have hinner : inner ℝ (physicalFieldL2 v hv) (physicalFieldL2 w hw) =
      ∫ x in unitCube, inner ℝ (v x) (w x) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [physicalFieldL2_coe v hv, physicalFieldL2_coe w hw] with x hx hy
    rw [hx, hy]
  have h := pow_le_pow_left₀
    (norm_nonneg (inner ℝ (physicalFieldL2 v hv) (physicalFieldL2 w hw)))
    (norm_inner_le_norm (𝕜 := ℝ) (physicalFieldL2 v hv) (physicalFieldL2 w hw)) 2
  rw [Real.norm_eq_abs, sq_abs, mul_pow,
    physicalFieldL2_norm_sq, physicalFieldL2_norm_sq, hinner] at h
  exact h

theorem FINITE_CONVECTION_ENERGY_LE_CHI0
    (N : ℕ) (c : FourierCoeff) (hreal : SpectralReality c) :
    physicalEnergy (convection (finiteSynthesis N c)) ≤
      finiteChi0 (cutoffModes N) c ^ 2 * coefficientDissipation N c := by
  have hv := finiteSynthesis_contDiff N c
  have hi : IntegrableOn (fun x => ‖convection (finiteSynthesis N c) x‖ ^ 2)
      unitCube volume :=
    ((convection_continuous hv).norm.pow 2).continuousOn.integrableOn_compact isCompact_unitCube
  have hD := gradientSquareDensity_integrableOn hv
  have hpoint (x : Vec) : ‖convection (finiteSynthesis N c) x‖ ^ 2 ≤
      finiteChi0 (cutoffModes N) c ^ 2 * gradientSquareDensity (finiteSynthesis N c) x := by
    exact (CONVECTION_NORM_SQ_LE_GRADIENT_DENSITY _ x).trans
      (mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg _) (FINITE_SYNTHESIS_NORM_LE_CHI0 N c x) 2)
        (gradientSquareDensity_nonneg _ x))
  rw [physicalEnergy_eq_integral_norm_sq]
  calc
    _ ≤ ∫ x in unitCube,
        finiteChi0 (cutoffModes N) c ^ 2 * gradientSquareDensity (finiteSynthesis N c) x :=
      integral_mono hi (hD.const_mul _) hpoint
    _ = _ := by
      rw [integral_const_mul, FINITE_PHYSICAL_REAL_ENSTROPHY_PARSEVAL N c hreal]

/-- The local analytic input to the exact enstrophy absorption is proved
for the actual projected Fourier-Galerkin nonlinear power. -/
theorem FINITE_ENSTROPHY_TRANSPORT_SQUARE_LE_CHI0
    (N : ℕ) (c : FourierCoeff)
    (hsupp : ∀ k, k ∉ cutoffModes N → ∀ i, c k i = 0)
    (hreal : SpectralReality c) (hsol : SpectralSolenoidal c) :
    coefficientEnstrophyNonlinearPower N c ^ 2 ≤
      finiteChi0 (cutoffModes N) c ^ 2 * coefficientDissipation N c *
        coefficientLaplacianSquare N c := by
  have hv := finiteSynthesis_contDiff N c
  have hlap : Continuous (laplacian (finiteSynthesis N c)) := by
    rw [finiteSynthesis_laplacian]
    exact (finiteSynthesis_contDiff N _).continuous
  have hpair := PHYSICAL_PAIRING_SQUARE_LE_ENERGY_PRODUCT
    (convection (finiteSynthesis N c)) (laplacian (finiteSynthesis N c))
    (convection_continuous hv) hlap
  have hZ : physicalEnergy (laplacian (finiteSynthesis N c)) =
      coefficientLaplacianSquare N c := by
    rw [physicalEnergy_eq_integral_norm_sq, finite_laplacian_integral_norm_sq N c hreal]
  rw [coefficientEnstrophyNonlinearPower_eq_physical N c hsupp hreal hsol, neg_sq]
  exact hpair.trans (by
    rw [hZ]
    exact mul_le_mul_of_nonneg_right (FINITE_CONVECTION_ENERGY_LE_CHI0 N c hreal)
      (coefficientLaplacianSquare_nonneg N c))

theorem GALERKIN_CHI0_CONTINUOUS
    {ν : ℝ} {a : Field} {N : ℕ} (g : GalerkinSolution ν a N) :
    ContinuousOn (fun t => finiteChi0 (cutoffModes N) (g.coeff t)) (Ici 0) := by
  unfold finiteChi0 complexVecNorm
  apply continuousOn_finset_sum
  intro k _
  apply Real.continuous_sqrt.comp_continuousOn
  apply continuousOn_finset_sum
  intro i _
  exact ((g.coefficient_continuous k i).norm).pow 2

theorem GALERKIN_H1_INITIAL_ENSTROPHY_BOUND
    {ν : ℝ} {N : ℕ} (a : CriticalSobolev 2)
    (hreal : SpectralReality (criticalCoeff 2 a))
    (g : GalerkinSolution ν (finiteSynthesis N (criticalCoeff 2 a)) N) :
    coefficientDissipation N (g.coeff 0) ≤ ‖a‖ ^ 2 := by
  simpa only [criticalEnergy_two_eq_coefficientDissipation] using
    criticalGalerkin_criticalEnergy_initial_le 2 a hreal g

/-- H1 restart data and the actual finite caloric budget suffice for
uniform enstrophy/Laplacian accumulation, with no extra nonlinear premise. -/
theorem CALORIC_H1_GALERKIN_ENSTROPHY_ACCUMULATION
    (ν : ℝ) (hν : 0 < ν) (a : CriticalSobolev 2)
    (hreal : SpectralReality (criticalCoeff 2 a)) (S : ℝ)
    (hbudget : ∀ (N : ℕ)
      (g : GalerkinSolution ν (finiteSynthesis N (criticalCoeff 2 a)) N),
      ∀ T : ℝ, 0 ≤ T →
        (∫ t in (0 : ℝ)..T, finiteChi0 (cutoffModes N) (g.coeff t) ^ 2) ≤ S) :
    ∀ T : ℝ, 0 ≤ T → ∀ (N : ℕ)
      (g : GalerkinSolution ν (finiteSynthesis N (criticalCoeff 2 a)) N),
      ∀ t ∈ Icc (0 : ℝ) T,
        coefficientDissipation N (g.coeff t) +
          ν * (∫ s in (0 : ℝ)..t, coefficientLaplacianSquare N (g.coeff s)) ≤
            ‖a‖ ^ 2 * Real.exp (S / ν) := by
  apply GALERKIN_ENSTROPHY_ACCUMULATION_OF_CONTROL ν hν
    (fun N => finiteSynthesis N (criticalCoeff 2 a))
    (fun N g t => finiteChi0 (cutoffModes N) (g.coeff t) ^ 2) (‖a‖ ^ 2) S
  · intro N g
    exact (GALERKIN_CHI0_CONTINUOUS g).pow 2
  · intro N g t _
    exact sq_nonneg _
  · intro N g t ht
    exact FINITE_ENSTROPHY_TRANSPORT_SQUARE_LE_CHI0 N (g.coeff t)
      (g.mode_support t ht) (g.real_symmetry t ht) (g.solenoidal t ht)
  · intro N g
    exact GALERKIN_H1_INITIAL_ENSTROPHY_BOUND a hreal g
  · exact hbudget

end
end QuasiFeffermanB
