import SingularClosure.FiniteParseval
import SingularClosure.CriticalInitialPhysicalFourier
import Mathlib.Tactic
import SingularityDisprovement.FejerCombinatorics

/-! A positive finite Fourier test kernel on the actual physical unit cube.
The definition is a squared finite character sum; positivity is pointwise,
and its normalization follows from the already audited orthogonality.
-/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory SingularClosure
open scoped BigOperators Topology ENNReal

namespace SingularityDisprovement
noncomputable section

def fejerAxis (n : ℤ) : Frequency := ![0, n, 0]

@[simp] theorem fejerAxis_inj {m n : ℤ} : fejerAxis m = fejerAxis n ↔ m = n := by
  constructor
  · intro h
    simpa [fejerAxis] using congrFun h (1 : Fin 3)
  · rintro rfl
    rfl

@[simp] theorem fejerAxis_zero : fejerAxis 0 = 0 := by
  ext i
  fin_cases i <;> simp [fejerAxis]

@[simp] theorem fejerAxis_sub (m n : ℤ) :
    fejerAxis (m - n) = fejerAxis m - fejerAxis n := by
  ext i
  fin_cases i <;> simp [fejerAxis]

def fejerSum (N : ℕ) (x : Vec) : ℂ :=
  ∑ j ∈ Finset.range N, fourierCharacter (fejerAxis (j : ℤ)) x

def fejerKernel (N : ℕ) (x : Vec) : ℝ :=
  Complex.normSq (fejerSum N x) / (N : ℝ)

theorem fejerSum_continuous (N : ℕ) : Continuous (fejerSum N) := by
  unfold fejerSum
  exact continuous_finsetSum _ (fun j _ => (fourierCharacter_contDiff _).continuous)

theorem fejerKernel_nonneg (N : ℕ) (x : Vec) : 0 ≤ fejerKernel N x := by
  exact div_nonneg (Complex.normSq_nonneg _) (Nat.cast_nonneg _)

theorem fejerKernel_continuous (N : ℕ) : Continuous (fejerKernel N) := by
  unfold fejerKernel
  exact (Complex.continuous_normSq.comp (fejerSum_continuous N)).div_const _

theorem fejerSum_star_mul_integral (N : ℕ) :
    (∫ x in unitCube, star (fejerSum N x) * fejerSum N x) = (N : ℂ) := by
  classical
  unfold fejerSum
  simp_rw [complex_star_finset_sum]
  rw [integral_unitCube_complex_sum_mul_sum (Finset.range N) (Finset.range N)
    (fun j x => star (fourierCharacter (fejerAxis (j : ℤ)) x))
    (fun k x => fourierCharacter (fejerAxis (k : ℤ)) x)
    (fun j => (fourierCharacter_contDiff _).continuous.star)
    (fun k => (fourierCharacter_contDiff _).continuous)]
  simp_rw [INTEGRAL_FOURIER_CHARACTER_ORTHOGONALITY, fejerAxis_inj]
  have hfilter : (Finset.range N).filter (fun x => x < N) = Finset.range N :=
    Finset.filter_eq_self.mpr (fun x hx => Finset.mem_range.mp hx)
  simp [hfilter]

theorem fejerSum_normSq_integral (N : ℕ) :
    (∫ x in unitCube, Complex.normSq (fejerSum N x)) = (N : ℝ) := by
  have hi : IntegrableOn
      (fun x : Vec => star (fejerSum N x) * fejerSum N x) unitCube volume :=
    ((fejerSum_continuous N).star.mul (fejerSum_continuous N)).continuousOn.integrableOn_compact
      isCompact_unitCube
  calc
    _ = ∫ x in unitCube, (star (fejerSum N x) * fejerSum N x).re := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      simpa only [Complex.ofReal_re, Complex.star_def] using
        congrArg Complex.re (Complex.normSq_eq_conj_mul_self (z := fejerSum N x))
    _ = (∫ x in unitCube, star (fejerSum N x) * fejerSum N x).re :=
      Complex.reCLM.integral_comp_comm hi
    _ = (N : ℝ) := by rw [fejerSum_star_mul_integral]; simp

theorem fejerKernel_integral (N : ℕ) (hN : 0 < N) :
    (∫ x in unitCube, fejerKernel N x) = 1 := by
  unfold fejerKernel
  rw [integral_div, fejerSum_normSq_integral]
  exact div_self (by exact_mod_cast (Nat.ne_of_gt hN))

theorem fejerKernel_integrable (N : ℕ) : IntegrableOn (fejerKernel N) unitCube volume :=
  (fejerKernel_continuous N).continuousOn.integrableOn_compact isCompact_unitCube

/-- The finite kernel is a sum of actual physical Fourier characters. -/
theorem fejerKernel_complex_expansion (N : ℕ) (x : Vec) :
    (fejerKernel N x : ℂ) =
      (∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N,
        star (fourierCharacter (fejerAxis (j : ℤ) - fejerAxis (k : ℤ)) x)) /
          (N : ℂ) := by
  unfold fejerKernel
  push_cast
  rw [Complex.normSq_eq_conj_mul_self]
  change star (fejerSum N x) * fejerSum N x / (N : ℂ) = _
  congr 1
  unfold fejerSum
  rw [complex_star_finset_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← fourierCharacter_neg, fourierCharacter_mul, ← fourierCharacter_neg]
  congr 1
  abel

/-- Integral against the finite positive kernel is a finite coefficient sum.
The integrability premises are genuine Fourier integrand premises. -/
theorem fejerKernel_weighted_integral_complex
    (a : Field) (ha : ∀ k : Frequency,
      IntegrableOn (datumFourierIntegrand a k 0) unitCube volume) (N : ℕ) :
    (∫ x in unitCube, (fejerKernel N x : ℂ) * (a x 0 : ℂ)) =
      (∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N,
        datumFourierCoeff a (fejerAxis (j : ℤ) - fejerAxis (k : ℤ)) 0) / (N : ℂ) := by
  classical
  have heq (x : Vec) : (fejerKernel N x : ℂ) * (a x 0 : ℂ) =
      (∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N,
        datumFourierIntegrand a (fejerAxis (j : ℤ) - fejerAxis (k : ℤ)) 0 x) /
        (N : ℂ) := by
    rw [fejerKernel_complex_expansion, div_mul_eq_mul_div]
    simp only [datumFourierIntegrand, Finset.sum_mul]
  simp_rw [heq]
  rw [integral_div]
  congr 1
  rw [integral_finsetSum (Finset.range N) (fun j _ =>
    integrable_finsetSum _ (fun k _ => ha _))]
  apply Finset.sum_congr rfl
  intro j hj
  rw [integral_finsetSum (Finset.range N) (fun k _ => ha _)]
  rfl

/-- Positive normalized tests preserve an a.e. scalar upper bound. -/
theorem fejerKernel_integral_mul_le
    (f : Vec → ℝ) (M : ℝ) (N : ℕ) (hN : 0 < N)
    (hf : IntegrableOn (fun x => fejerKernel N x * f x) unitCube volume)
    (hbound : ∀ᵐ x ∂volume.restrict unitCube, f x ≤ M) :
    (∫ x in unitCube, fejerKernel N x * f x) ≤ M := by
  calc
    _ ≤ ∫ x in unitCube, fejerKernel N x * M :=
      integral_mono_ae hf ((fejerKernel_integrable N).mul_const M)
        (hbound.mono (fun x hx => mul_le_mul_of_nonneg_left hx (fejerKernel_nonneg N x)))
    _ = M := by rw [integral_mul_const, fejerKernel_integral N hN, one_mul]

/-- Every actual physical L2 representative has integrable Fourier integrands. -/
theorem physicalCube_fourierIntegrand_integrable
    (v : PhysicalCubeL2) (k : Frequency) (i : Fin 3) :
    IntegrableOn (datumFourierIntegrand (v : Field) k i) unitCube volume := by
  have hi := L2.integrable_inner (𝕜 := ℂ) (criticalCubeCharacterL2 k)
    ((criticalCubeComplexCoordinate i).compLpL 2 (volume.restrict unitCube) v)
  apply hi.congr
  have hchar := (critical_continuous_memLp_cube (fourierCharacter k)
    (fourierCharacter_contDiff k).continuous 2).coeFn_toLp
  have hcoord := (criticalCubeComplexCoordinate i).coeFn_compLpL v
  filter_upwards [hchar, hcoord] with x hx hxi
  change inner ℂ (criticalCubeCharacterL2 k x)
      (((criticalCubeComplexCoordinate i).compLpL 2 (volume.restrict unitCube) v) x) = _
  change criticalCubeCharacterL2 k x = fourierCharacter k x at hx
  rw [hx, hxi]
  simp only [criticalCubeComplexCoordinate, ContinuousLinearMap.comp_apply,
    EuclideanSpace.coe_proj, Complex.ofRealCLM_apply, RCLike.inner_apply,
    Complex.star_def, datumFourierIntegrand, mul_comm]

theorem fejerKernel_weighted_integrable_complex
    (a : Field) (ha : ∀ k : Frequency,
      IntegrableOn (datumFourierIntegrand a k 0) unitCube volume) (N : ℕ) :
    IntegrableOn (fun x => (fejerKernel N x : ℂ) * (a x 0 : ℂ)) unitCube volume := by
  have hi : IntegrableOn (fun x =>
      (∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N,
        datumFourierIntegrand a (fejerAxis (j : ℤ) - fejerAxis (k : ℤ)) 0 x) /
        (N : ℂ)) unitCube volume :=
    (integrable_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ => ha _))).div_const _
  apply hi.congr
  apply Filter.Eventually.of_forall
  intro x
  dsimp only
  rw [fejerKernel_complex_expansion, div_mul_eq_mul_div]
  simp only [datumFourierIntegrand, Finset.sum_mul]

theorem fejerKernel_weighted_integrable_real
    (a : Field) (ha : ∀ k : Frequency,
      IntegrableOn (datumFourierIntegrand a k 0) unitCube volume) (N : ℕ) :
    IntegrableOn (fun x => fejerKernel N x * a x 0) unitCube volume := by
  have hi := (fejerKernel_weighted_integrable_complex a ha N).re
  change Integrable
    (fun x => ((fejerKernel N x : ℂ) * (a x 0 : ℂ)).re)
    (volume.restrict unitCube) at hi
  simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero] using hi

theorem fejerKernel_weighted_integral_real
    (a : Field) (ha : ∀ k : Frequency,
      IntegrableOn (datumFourierIntegrand a k 0) unitCube volume) (N : ℕ) :
    (∫ x in unitCube, fejerKernel N x * a x 0) =
      ((∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N,
        datumFourierCoeff a (fejerAxis (j : ℤ) - fejerAxis (k : ℤ)) 0) / (N : ℂ)).re := by
  have h := Complex.reCLM.integral_comp_comm
    (fejerKernel_weighted_integrable_complex a ha N)
  simpa only [Complex.reCLM_apply, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero,
    fejerKernel_weighted_integral_complex a ha N] using h

theorem fejerKernel_weighted_integral_eq_average
    (a : PhysicalCubeL2) (N : ℕ) :
    (∫ x in unitCube, fejerKernel N x * a x 0) =
      fejerCoefficientAverage
        (fun n : ℤ => (datumFourierCoeff (a : Field) (fejerAxis n) 0).re) N := by
  rw [fejerKernel_weighted_integral_real (a : Field)
    (fun k => physicalCube_fourierIntegrand_integrable a k 0) N]
  change ((∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N,
    datumFourierCoeff (a : Field) (fejerAxis (j : ℤ) - fejerAxis (k : ℤ)) 0) /
    ((N : ℝ) : ℂ)).re = _
  rw [Complex.div_ofReal_re]
  simp_rw [physical_complex_re_sum, ← fejerAxis_sub]
  unfold fejerCoefficientAverage
  congr 1
  exact Finset.sum_comm

theorem fejerAverage_le_of_component_ae_le
    (a : PhysicalCubeL2) (B : ℝ)
    (hbound : ∀ᵐ x ∂volume.restrict unitCube, a x 0 ≤ B)
    (N : ℕ) (hN : 0 < N) :
    fejerCoefficientAverage
      (fun n : ℤ => (datumFourierCoeff (a : Field) (fejerAxis n) 0).re) N ≤ B := by
  rw [← fejerKernel_weighted_integral_eq_average]
  exact fejerKernel_integral_mul_le (fun x => a x 0) B N hN
    (fejerKernel_weighted_integrable_real (a : Field)
      (fun k => physicalCube_fourierIntegrand_integrable a k 0) N) hbound

end
end SingularityDisprovement
