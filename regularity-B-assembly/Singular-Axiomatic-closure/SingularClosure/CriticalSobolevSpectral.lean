import SingularClosure.CriticalSobolevAnalytic
import SingularClosure.CriticalFourierInterpolation
import SingularClosure.FiniteParseval

/-! The literal finite Fourier analytic family interpolating the energy
and dissipation endpoint estimates.  Both boundary energies are exactly
the homogeneous H^(1/2) coefficient energy. -/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory
open scoped BigOperators

namespace SingularClosure
noncomputable section

def criticalSpectralCoeff (z : ℂ) (c : FourierCoeff) : FourierCoeff :=
  fun k i => criticalComplexWeight (criticalFrequencyWeight k) ((1 / 2 : ℂ) - z) * c k i

def criticalSpectralDerivativeCoeff (z : ℂ) (c : FourierCoeff) : FourierCoeff :=
  fun k i => -(Real.log (criticalFrequencyWeight k) : ℂ) * criticalSpectralCoeff z c k i

def criticalSpectralFamily (N : ℕ) (c : FourierCoeff) (j : Fin 3)
    (z : ℂ) (x : Vec) : ℂ :=
  complexFiniteSynthesis N (criticalSpectralCoeff z c) j x

def criticalSpectralDerivative (N : ℕ) (c : FourierCoeff) (j : Fin 3)
    (z : ℂ) (x : Vec) : ℂ :=
  complexFiniteSynthesis N (criticalSpectralDerivativeCoeff z c) j x

theorem criticalSpectralCoeff_continuous (c : FourierCoeff) (k : Frequency) (i : Fin 3) :
    Continuous (fun z => criticalSpectralCoeff z c k i) := by
  unfold criticalSpectralCoeff criticalComplexWeight
  fun_prop

theorem criticalSpectralDerivativeCoeff_continuous
    (c : FourierCoeff) (k : Frequency) (i : Fin 3) :
    Continuous (fun z => criticalSpectralDerivativeCoeff z c k i) :=
  continuous_const.mul (criticalSpectralCoeff_continuous c k i)

theorem criticalSpectralFamily_continuous (N : ℕ) (c : FourierCoeff) (j : Fin 3) :
    Continuous (fun q : ℂ × Vec => criticalSpectralFamily N c j q.1 q.2) :=
  continuous_finsetSum _ (fun k _ =>
    ((fourierCharacter_contDiff k).continuous.comp continuous_snd).mul
      ((criticalSpectralCoeff_continuous c k j).comp continuous_fst))

theorem criticalSpectralDerivative_continuous (N : ℕ) (c : FourierCoeff) (j : Fin 3) :
    Continuous (fun q : ℂ × Vec => criticalSpectralDerivative N c j q.1 q.2) :=
  continuous_finsetSum _ (fun k _ =>
    ((fourierCharacter_contDiff k).continuous.comp continuous_snd).mul
      ((criticalSpectralDerivativeCoeff_continuous c k j).comp continuous_fst))

theorem criticalSpectralCoeff_hasDerivAt
    (c : FourierCoeff) (k : Frequency) (i : Fin 3) (z : ℂ) :
    HasDerivAt (fun w => criticalSpectralCoeff w c k i)
      (criticalSpectralDerivativeCoeff z c k i) z := by
  have h := ((criticalComplexWeight_hasDerivAt (criticalFrequencyWeight k)
      ((1 / 2 : ℂ) - z)).comp z ((hasDerivAt_id z).const_sub (1 / 2))).mul_const (c k i)
  convert! h using 1 <;> simp only [criticalSpectralCoeff, criticalSpectralDerivativeCoeff] <;> ring

theorem criticalSpectralFamily_hasDerivAt
    (N : ℕ) (c : FourierCoeff) (j : Fin 3) (z : ℂ) (x : Vec) :
    HasDerivAt (fun w => criticalSpectralFamily N c j w x)
      (criticalSpectralDerivative N c j z x) z := by
  unfold criticalSpectralFamily criticalSpectralDerivative complexFiniteSynthesis
  exact HasDerivAt.fun_sum fun k _ =>
    (criticalSpectralCoeff_hasDerivAt c k j z).const_mul (fourierCharacter k x)

@[simp]
theorem criticalSpectralCoeff_midpoint (c : FourierCoeff) :
    criticalSpectralCoeff (1 / 2) c = c := by
  funext k i
  simp [criticalSpectralCoeff]

@[simp]
theorem criticalSpectralFamily_midpoint (N : ℕ) (c : FourierCoeff) (j : Fin 3) :
    criticalSpectralFamily N c j (1 / 2) = complexFiniteSynthesis N c j := by
  simp only [criticalSpectralFamily, criticalSpectralCoeff_midpoint]

theorem criticalSpectralCoeff_normSq (z : ℂ) (c : FourierCoeff)
    (k : Frequency) (i : Fin 3) :
    Complex.normSq (criticalSpectralCoeff z c k i) =
      criticalFrequencyWeight k ^ (1 - 2 * z.re) * Complex.normSq (c k i) := by
  rw [criticalSpectralCoeff, Complex.normSq_mul, Complex.normSq_eq_norm_sq,
    criticalComplexWeight_norm (criticalFrequencyWeight_pos k)]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul (criticalFrequencyWeight_pos k).le]
  congr 1
  simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re]
  ring

theorem criticalSpectral_left_energy (N : ℕ) (c : FourierCoeff)
    {z : ℂ} (hz : z.re = 0) :
    coefficientEnergy N (criticalSpectralCoeff z c) = criticalEnergy 1 N c := by
  unfold coefficientEnergy criticalEnergy
  simp_rw [criticalSpectralCoeff_normSq, hz]
  simp

theorem criticalSpectral_right_dissipation (N : ℕ) (c : FourierCoeff)
    {z : ℂ} (hz : z.re = 1) :
    coefficientDissipation N (criticalSpectralCoeff z c) = criticalEnergy 1 N c := by
  unfold coefficientDissipation criticalEnergy
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro i _
  have hk0 : k ≠ 0 := ((mem_cutoffModes_iff N k).mp hk).2.1
  rw [criticalSpectralCoeff_normSq, hz]
  norm_num only [mul_one, show (1 : ℝ) - 2 = -1 by norm_num, Real.rpow_neg_one, pow_one]
  change laplacianFrequency k * ((criticalFrequencyWeight k)⁻¹ * Complex.normSq (c k i)) = _
  rw [← criticalFrequencyWeight_sq_of_ne_zero k hk0]
  field_simp [(criticalFrequencyWeight_pos k).ne']

theorem criticalSpectralFamily_strip_bound (N : ℕ) (c : FourierCoeff) (j : Fin 3) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 →
      ∀ x ∈ unitCube, ‖criticalSpectralFamily N c j z x‖ ≤ M := by
  refine ⟨∑ k ∈ cutoffModes N, Real.sqrt (criticalFrequencyWeight k) * ‖c k j‖,
    Finset.sum_nonneg (fun k _ => mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)), ?_⟩
  intro z hz _ x _
  unfold criticalSpectralFamily complexFiniteSynthesis
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro k _
  rw [norm_mul, fourierCharacter_norm, one_mul, criticalSpectralCoeff, norm_mul,
    criticalComplexWeight_norm (criticalFrequencyWeight_pos k), Real.sqrt_eq_rpow]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply Real.rpow_le_rpow_of_exponent_le (criticalFrequencyWeight_one_le k)
  simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re]
  linarith

end
end SingularClosure
