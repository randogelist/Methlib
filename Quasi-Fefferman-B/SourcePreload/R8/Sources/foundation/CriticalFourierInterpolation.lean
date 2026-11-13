import SingularClosure.GalerkinEnergy
import SingularClosure.CriticalSpaces
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! Finite homogeneous Fourier interpolation with constant one. The proof
uses only nonnegative frequency weights and finite Cauchy--Schwarz. -/

set_option autoImplicit false
set_option Elab.async true

open scoped BigOperators

namespace SingularClosure

noncomputable section

theorem finite_weighted_nonnegative_interpolation {ι : Type*}
    (s : Finset ι) (w a : ι → ℝ)
    (hw : ∀ k ∈ s, 0 ≤ w k) (ha : ∀ k ∈ s, 0 ≤ a k) :
    (∑ k ∈ s, w k ^ 2 * a k) ^ 2 ≤
      (∑ k ∈ s, w k * a k) * ∑ k ∈ s, w k ^ 3 * a k := by
  refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
    (r := fun k => w k ^ 2 * a k)
    (f := fun k => w k * a k)
    (g := fun k => w k ^ 3 * a k) ?_ ?_ ?_
  · intro k hk
    exact mul_nonneg (hw k hk) (ha k hk)
  · intro k hk
    exact mul_nonneg (pow_nonneg (hw k hk) 3) (ha k hk)
  · intro k _
    exact le_of_eq (by ring)

theorem finite_weighted_fourier_interpolation {ι : Type*}
    (s : Finset ι) (w : ι → ℝ) (c : ι → ℂ)
    (hw : ∀ k ∈ s, 0 ≤ w k) :
    (∑ k ∈ s, w k ^ 2 * ‖c k‖ ^ 2) ^ 2 ≤
      (∑ k ∈ s, w k * ‖c k‖ ^ 2) * ∑ k ∈ s, w k ^ 3 * ‖c k‖ ^ 2 :=
  finite_weighted_nonnegative_interpolation s w (fun k => ‖c k‖ ^ 2) hw
    (fun k _ => sq_nonneg ‖c k‖)

theorem finite_vector_weighted_fourier_interpolation
    (s : Finset Frequency) (w : Frequency → ℝ) (c : FourierCoeff)
    (hw : ∀ k ∈ s, 0 ≤ w k) :
    (∑ k ∈ s, ∑ i : Fin 3, w k ^ 2 * Complex.normSq (c k i)) ^ 2 ≤
      (∑ k ∈ s, ∑ i : Fin 3, w k * Complex.normSq (c k i)) *
        ∑ k ∈ s, ∑ i : Fin 3, w k ^ 3 * Complex.normSq (c k i) := by
  have h := finite_weighted_nonnegative_interpolation s w
    (fun k => ∑ i : Fin 3, Complex.normSq (c k i)) hw
    (fun k _ => Finset.sum_nonneg (fun i _ => Complex.normSq_nonneg (c k i)))
  simpa only [Finset.mul_sum] using h

theorem finite_weighted_fourier_interpolation_sqrt {ι : Type*}
    (s : Finset ι) (w : ι → ℝ) (c : ι → ℂ)
    (hw : ∀ k ∈ s, 0 ≤ w k) :
    (∑ k ∈ s, w k ^ 2 * ‖c k‖ ^ 2) ≤
      Real.sqrt (∑ k ∈ s, w k * ‖c k‖ ^ 2) *
        Real.sqrt (∑ k ∈ s, w k ^ 3 * ‖c k‖ ^ 2) := by
  have hmiddle : 0 ≤ ∑ k ∈ s, w k ^ 2 * ‖c k‖ ^ 2 :=
    Finset.sum_nonneg (fun k _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hlower : 0 ≤ ∑ k ∈ s, w k * ‖c k‖ ^ 2 :=
    Finset.sum_nonneg (fun k hk => mul_nonneg (hw k hk) (sq_nonneg _))
  have hupper : 0 ≤ ∑ k ∈ s, w k ^ 3 * ‖c k‖ ^ 2 :=
    Finset.sum_nonneg (fun k hk => mul_nonneg (pow_nonneg (hw k hk) 3) (sq_nonneg _))
  apply (sq_le_sq₀ hmiddle (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt hlower, Real.sq_sqrt hupper]
  exact finite_weighted_fourier_interpolation s w c hw

/-- The exponent q is twice the homogeneous Sobolev order. -/
def criticalEnergy (q N : ℕ) (c : FourierCoeff) : ℝ :=
  ∑ k ∈ cutoffModes N, ∑ i : Fin 3,
    criticalFrequencyWeight k ^ q * Complex.normSq (c k i)

theorem criticalEnergy_nonneg (q N : ℕ) (c : FourierCoeff) :
    0 ≤ criticalEnergy q N c := by
  have hw (k : Frequency) : 0 ≤ criticalFrequencyWeight k := by
    unfold criticalFrequencyWeight
    split
    · norm_num
    · exact Real.sqrt_nonneg _
  unfold criticalEnergy
  apply Finset.sum_nonneg
  intro k _
  exact Finset.sum_nonneg (fun i _ =>
    mul_nonneg (pow_nonneg (hw k) q) (Complex.normSq_nonneg (c k i)))

/-- The actual finite H1 energy interpolates between H(1/2) and H(3/2). -/
theorem criticalEnergy_interpolation (N : ℕ) (c : FourierCoeff) :
    criticalEnergy 2 N c ^ 2 ≤ criticalEnergy 1 N c * criticalEnergy 3 N c := by
  have hw (k : Frequency) (_ : k ∈ cutoffModes N) : 0 ≤ criticalFrequencyWeight k := by
    unfold criticalFrequencyWeight
    split
    · norm_num
    · exact Real.sqrt_nonneg _
  simpa only [criticalEnergy, pow_one] using
    finite_vector_weighted_fourier_interpolation (cutoffModes N) criticalFrequencyWeight c hw

theorem criticalEnergy_interpolation_sqrt (N : ℕ) (c : FourierCoeff) :
    criticalEnergy 2 N c ≤
      Real.sqrt (criticalEnergy 1 N c) * Real.sqrt (criticalEnergy 3 N c) := by
  apply (sq_le_sq₀ (criticalEnergy_nonneg 2 N c)
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt (criticalEnergy_nonneg 1 N c),
    Real.sq_sqrt (criticalEnergy_nonneg 3 N c)]
  exact criticalEnergy_interpolation N c

/-- The cutoff excludes zero, so the modified zero-mode weight does not occur. -/
theorem criticalEnergy_two_eq_coefficientDissipation (N : ℕ) (c : FourierCoeff) :
    criticalEnergy 2 N c = coefficientDissipation N c := by
  unfold criticalEnergy coefficientDissipation
  apply Finset.sum_congr rfl
  intro k hk
  have hk0 : k ≠ 0 := ((mem_cutoffModes_iff N k).mp hk).2.1
  have hfreq : 0 ≤ laplacianFrequency k := by
    unfold laplacianFrequency
    exact mul_nonneg (sq_nonneg _) (by exact_mod_cast galerkinFreqSq_nonneg k)
  have hw : criticalFrequencyWeight k ^ 2 = laplacianFrequency k := by
    rw [criticalFrequencyWeight, if_neg hk0, Real.sq_sqrt hfreq]
  apply Finset.sum_congr rfl
  intro i _
  simp only [hw, laplacianFrequency]

theorem coefficientDissipation_sq_le_criticalEnergy (N : ℕ) (c : FourierCoeff) :
    coefficientDissipation N c ^ 2 ≤ criticalEnergy 1 N c * criticalEnergy 3 N c := by
  rw [← criticalEnergy_two_eq_coefficientDissipation]
  exact criticalEnergy_interpolation N c

end

end SingularClosure
