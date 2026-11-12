import SingularClosure.CriticalSobolevSpectral
import SingularClosure.CriticalSobolevInterpolation
import SingularClosure.CriticalSobolevMass
import SingularClosure.CriticalComplexSobolev
import SingularClosure.CriticalSobolevVector

/-! Cutoff-independent critical Fourier Sobolev embedding.  The L3 bound
is obtained from the actual finite analytic family and its L2/L6 boundary
bounds.  The regularized dual mass is then sent to its literal limit. -/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory
open scoped ENNReal

namespace SingularClosure
noncomputable section

theorem criticalSpectral_left_lpNorm (N : ℕ) (c : FourierCoeff) (j : Fin 3)
    {z : ℂ} (hz : z.re = 0) :
    lpNorm (criticalSpectralFamily N c j z) 2 (volume.restrict unitCube) ≤
      Real.sqrt (criticalEnergy 1 N c) := by
  have h := CRITICAL_COMPLEX_FINITE_L2 N (criticalSpectralCoeff z c) j
  rw [criticalSpectral_left_energy N c hz] at h
  have ht : (ENNReal.ofReal (criticalEnergy 1 N c)) ^ (1 / 2 : ℝ) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
  have hr := ENNReal.toReal_mono ht h
  rw [toReal_eLpNorm (complexFiniteSynthesis_continuous N _ j).aestronglyMeasurable,
    ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal (criticalEnergy_nonneg 1 N c),
    ← Real.sqrt_eq_rpow] at hr
  exact hr

theorem criticalSpectral_right_lpNorm (C : ℝ≥0∞) (hC : C < ⊤)
    (hL6 : ∀ (N : ℕ) (c : FourierCoeff) (j : Fin 3),
      eLpNorm (complexFiniteSynthesis N c j) 6 (volume.restrict unitCube) ≤
        C * (ENNReal.ofReal (coefficientDissipation N c)) ^ (1 / 2 : ℝ))
    (N : ℕ) (c : FourierCoeff) (j : Fin 3) {z : ℂ} (hz : z.re = 1) :
    lpNorm (criticalSpectralFamily N c j z) 6 (volume.restrict unitCube) ≤
      C.toReal * Real.sqrt (criticalEnergy 1 N c) := by
  have h := hL6 N (criticalSpectralCoeff z c) j
  rw [criticalSpectral_right_dissipation N c hz] at h
  have ht : C * (ENNReal.ofReal (criticalEnergy 1 N c)) ^ (1 / 2 : ℝ) ≠ ⊤ := by
    exact ENNReal.mul_ne_top hC.ne
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)
  have hr := ENNReal.toReal_mono ht h
  rw [toReal_eLpNorm (complexFiniteSynthesis_continuous N _ j).aestronglyMeasurable,
    ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal (criticalEnergy_nonneg 1 N c), ← Real.sqrt_eq_rpow] at hr
  exact hr

theorem critical_complex_lpNorm_three_bound (C : ℝ≥0∞) (hC : C < ⊤)
    (hL6 : ∀ (N : ℕ) (c : FourierCoeff) (j : Fin 3),
      eLpNorm (complexFiniteSynthesis N c j) 6 (volume.restrict unitCube) ≤
        C * (ENNReal.ofReal (coefficientDissipation N c)) ^ (1 / 2 : ℝ))
    (N : ℕ) (c : FourierCoeff) (j : Fin 3) :
    lpNorm (complexFiniteSynthesis N c j) 3 (volume.restrict unitCube) ≤
      Real.sqrt C.toReal * Real.sqrt (criticalEnergy 1 N c) := by
  let A : ℝ := Real.sqrt (criticalEnergy 1 N c)
  let B : ℝ := C.toReal * Real.sqrt (criticalEnergy 1 N c)
  have hA : 0 ≤ A := Real.sqrt_nonneg _
  have hB : 0 ≤ B := mul_nonneg ENNReal.toReal_nonneg (Real.sqrt_nonneg _)
  have hmid : Real.sqrt A * Real.sqrt B =
      Real.sqrt C.toReal * Real.sqrt (criticalEnergy 1 N c) := by
    dsimp [A, B]
    rw [Real.sqrt_mul ENNReal.toReal_nonneg]
    calc
      _ = Real.sqrt C.toReal *
          (Real.sqrt (Real.sqrt (criticalEnergy 1 N c)) *
            Real.sqrt (Real.sqrt (criticalEnergy 1 N c))) := by ring
      _ = _ := by rw [Real.mul_self_sqrt (Real.sqrt_nonneg _)]
  have hcancel := critical_cubic_mass_cancel (complexFiniteSynthesis N c j)
    (complexFiniteSynthesis_continuous N c j)
    (K := Real.sqrt A * Real.sqrt B)
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (by
      intro δ hδ
      have h := critical_analytic_family_regularized_bound
        (criticalSpectralFamily N c j) (criticalSpectralDerivative N c j)
        (criticalSpectralFamily_continuous N c j)
        (criticalSpectralDerivative_continuous N c j)
        (criticalSpectralFamily_hasDerivAt N c j)
        (criticalSpectralFamily_strip_bound N c j)
        A B hA hB
        (fun z hz => criticalSpectral_left_lpNorm N c j hz)
        (fun z hz => criticalSpectral_right_lpNorm C hC hL6 N c j hz)
        δ hδ
      simpa only [criticalSpectralFamily_midpoint, criticalDualMass, criticalDualBase] using h)
  rw [hmid] at hcancel
  simpa only [lpNorm_eq_integral_norm_rpow_toReal
      (by norm_num : (3 : ℝ≥0∞) ≠ 0) (by norm_num : (3 : ℝ≥0∞) ≠ ⊤)
        (complexFiniteSynthesis_continuous N c j).aestronglyMeasurable,
    ENNReal.toReal_ofNat, Real.rpow_ofNat, one_div] using hcancel

/-- The complex scalar critical embedding, with one constant for every
cutoff, coefficient family, and vector component. -/
theorem CRITICAL_COMPLEX_FINITE_L3 :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (N : ℕ) (c : FourierCoeff) (j : Fin 3),
      eLpNorm (complexFiniteSynthesis N c j) 3 (volume.restrict unitCube) ≤
        C * (ENNReal.ofReal (criticalEnergy 1 N c)) ^ (1 / 2 : ℝ) := by
  obtain ⟨K, hK, hL6⟩ := CRITICAL_COMPLEX_FINITE_L6
  refine ⟨ENNReal.ofReal (Real.sqrt K.toReal), ENNReal.ofReal_lt_top, ?_⟩
  intro N c j
  rw [← ofReal_lpNorm (critical_continuous_memLp_cube _
    (complexFiniteSynthesis_continuous N c j) 3)]
  calc
    _ ≤ ENNReal.ofReal (Real.sqrt K.toReal * Real.sqrt (criticalEnergy 1 N c)) :=
      ENNReal.ofReal_le_ofReal (critical_complex_lpNorm_three_bound K hK hL6 N c j)
    _ = _ := by
      rw [ENNReal.ofReal_mul (Real.sqrt_nonneg _),
        Real.sqrt_eq_rpow (criticalEnergy 1 N c),
        ENNReal.ofReal_rpow_of_nonneg (criticalEnergy_nonneg 1 N c) (by norm_num)]

/-- Actual cutoff-independent homogeneous H^(1/2) to L3 embedding for the
finite real Fourier polynomial, without a conjugate-reality premise. -/
theorem FINITE_CRITICAL_HHALF_L3 :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (N : ℕ) (c : FourierCoeff),
      eLpNorm (finiteSynthesis N c) 3 (volume.restrict unitCube) ≤
        C * (ENNReal.ofReal (criticalEnergy 1 N c)) ^ (1 / 2 : ℝ) := by
  obtain ⟨C, hC, hscalar⟩ := CRITICAL_COMPLEX_FINITE_L3
  refine ⟨3 * C, ?_, ?_⟩
  · exact ENNReal.mul_lt_top (by norm_num) hC
  · exact critical_vector_L3_of_scalar hscalar

end
end SingularClosure
