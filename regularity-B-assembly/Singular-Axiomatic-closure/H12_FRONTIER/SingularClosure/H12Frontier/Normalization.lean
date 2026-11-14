import SingularClosure.CriticalSpaces
import Mathlib

/-! Exact coefficient/native normalization. No nonlinear estimate is assumed. -/
set_option autoImplicit false
set_option Elab.async true

open scoped BigOperators
namespace SingularClosure.H12Frontier
noncomputable section

/-- The Euclidean length of the integer Fourier frequency. -/
def paperFrequency (k : Frequency) : ℝ := Real.sqrt (galerkinFreqSq k : ℝ)

/-- The literal coefficient norm square, with no 2*pi in the weight. -/
def paperNormSq (q : ℕ) (a : CriticalSobolev (q : ℤ)) : ℝ :=
  ∑' ki : FourierIndex,
    paperFrequency ki.1 ^ q * Complex.normSq (criticalCoeff (q : ℤ) a ki.1 ki.2)

def paperNorm (q : ℕ) (a : CriticalSobolev (q : ℤ)) : ℝ :=
  Real.sqrt (paperNormSq q a)

theorem paperNormSq_nonneg (q : ℕ) (a : CriticalSobolev (q : ℤ)) :
    0 ≤ paperNormSq q a :=
  tsum_nonneg (fun ki => mul_nonneg (pow_nonneg (Real.sqrt_nonneg _) q)
    (Complex.normSq_nonneg _))

theorem paperNorm_sq (q : ℕ) (a : CriticalSobolev (q : ℤ)) :
    paperNorm q a ^ 2 = paperNormSq q a :=
  Real.sq_sqrt (paperNormSq_nonneg q a)

theorem criticalFrequencyWeight_eq_paper (k : Frequency) (hk : k ≠ 0) :
    criticalFrequencyWeight k = (2 * Real.pi) * paperFrequency k := by
  rw [criticalFrequencyWeight, if_neg hk]
  unfold laplacianFrequency paperFrequency
  rw [Real.sqrt_mul (sq_nonneg (2 * Real.pi)),
    Real.sqrt_sq (by positivity : 0 ≤ 2 * Real.pi)]

theorem nativeNormSq_eq_paperNormSq (q : ℕ) (a : CriticalSobolev (q : ℤ))
    (hz : SpectralMeanZero (criticalCoeff (q : ℤ) a)) :
    ‖a‖ ^ 2 = (2 * Real.pi) ^ q * paperNormSq q a := by
  rw [criticalSobolev_norm_sq]
  simp only [zpow_natCast]
  calc
    (∑' ki : FourierIndex,
        criticalFrequencyWeight ki.1 ^ q *
          Complex.normSq (criticalCoeff (q : ℤ) a ki.1 ki.2)) =
        ∑' ki : FourierIndex, (2 * Real.pi) ^ q *
          (paperFrequency ki.1 ^ q *
            Complex.normSq (criticalCoeff (q : ℤ) a ki.1 ki.2)) := by
      apply tsum_congr
      rintro ⟨k, i⟩
      by_cases hk : k = 0
      · subst k
        change ∀ i : Fin 3, criticalCoeff (q : ℤ) a 0 i = 0 at hz
        simp only [hz i, Complex.normSq_zero, mul_zero]
      · rw [criticalFrequencyWeight_eq_paper k hk, mul_pow]
        ring
    _ = (2 * Real.pi) ^ q * paperNormSq q a := by
      rw [tsum_mul_left]
      rfl

theorem nativeNorm_eq_paperNorm (q : ℕ) (a : CriticalSobolev (q : ℤ))
    (hz : SpectralMeanZero (criticalCoeff (q : ℤ) a)) :
    ‖a‖ = Real.sqrt ((2 * Real.pi) ^ q) * paperNorm q a := by
  calc
    ‖a‖ = Real.sqrt (‖a‖ ^ 2) := (Real.sqrt_sq (norm_nonneg a)).symm
    _ = Real.sqrt ((2 * Real.pi) ^ q * paperNormSq q a) := by
      rw [nativeNormSq_eq_paperNormSq q a hz]
    _ = Real.sqrt ((2 * Real.pi) ^ q) * paperNorm q a := by
      rw [Real.sqrt_mul (by positivity : 0 ≤ (2 * Real.pi) ^ q)]
      rfl

/-- E01: one exact norm bridge, including both critical orders q=1 and q=3. -/
theorem FRONTIER_H12_NORM_BRIDGE (q : ℕ) (a : CriticalSobolev (q : ℤ))
    (hz : SpectralMeanZero (criticalCoeff (q : ℤ) a)) :
    ‖a‖ ^ 2 = (2 * Real.pi) ^ q * paperNormSq q a ∧
      paperNorm q a ^ 2 = paperNormSq q a ∧
      ‖a‖ = Real.sqrt ((2 * Real.pi) ^ q) * paperNorm q a :=
  ⟨nativeNormSq_eq_paperNormSq q a hz, paperNorm_sq q a,
    nativeNorm_eq_paperNorm q a hz⟩

theorem nativeHhalf_norm (a : CriticalSobolev 1)
    (hz : SpectralMeanZero (criticalCoeff 1 a)) :
    ‖a‖ = Real.sqrt (2 * Real.pi) * paperNorm 1 a := by
  simpa only [pow_one] using nativeNorm_eq_paperNorm 1 a hz

theorem nativeHthreeHalf_norm (a : CriticalSobolev 3)
    (hz : SpectralMeanZero (criticalCoeff 3 a)) :
    ‖a‖ = (2 * Real.pi) * Real.sqrt (2 * Real.pi) * paperNorm 3 a := by
  have hs : Real.sqrt ((2 * Real.pi) ^ 3) =
      (2 * Real.pi) * Real.sqrt (2 * Real.pi) := by
    apply (sq_eq_sq₀ (Real.sqrt_nonneg _)
      (mul_nonneg (by positivity) (Real.sqrt_nonneg _))).mp
    rw [Real.sq_sqrt (by positivity : 0 ≤ (2 * Real.pi) ^ 3)]
    simp only [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 2 * Real.pi)]
    ring
  simpa only [hs] using nativeNorm_eq_paperNorm 3 a hz

end
end SingularClosure.H12Frontier
