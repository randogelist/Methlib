import HVR_PrimeMomentJacobi

/-!
Finite-prime analogue of the finite trace-to-kernel step in snditeration's
`ManuscriptChain.LaplaceJacobiIdentity.trace_eq_kernel_integral`.
The sum is over the existing HVR prime cutoff with its actual prime weight;
the matrix inverse is Lean's nonsingular inverse. All-dimensional log-det
differentiation requires the determinant-nonzero assumption already present
in `HVRPrimeMomentJacobi.finite_prime_gram_logDet_hasDerivAt`.
No infinite limit or equality to the zeta log-derivative is asserted.

Independent finite-sum adaptation; this is a candidate pending external
cached Lean 4.34.0-rc1 compilation and theorem-level audit.
-/

noncomputable section
open scoped BigOperators
open Matrix

namespace HVRPrimeKernelTrace

open HVRPrimeGram HVRPrimeMomentJacobi

/-- Finite inverse-Gram kernel at an actual logarithmic prime node. -/
def diagonalKernel (N h : ℕ) (σ : ℝ) (p : ℕ) : ℝ :=
  ∑ i : Fin h, ∑ j : Fin h,
    ((gram N h σ)⁻¹) i j * (Real.log (p : ℝ)) ^ j.val *
      (Real.log (p : ℝ)) ^ i.val

/-- The shifted moment trace is the weighted finite kernel sum. -/
theorem trace_shifted_eq_prime_kernel_sum (N h : ℕ) (σ : ℝ) :
    (((gram N h σ)⁻¹ * shiftedGram N h σ).trace) =
      ∑ p ∈ primesUpTo N,
        primeWeight σ p * Real.log (p : ℝ) * diagonalKernel N h σ p := by
  classical
  calc
    (((gram N h σ)⁻¹ * shiftedGram N h σ).trace) =
        ∑ i : Fin h, ∑ j : Fin h,
          ∑ p ∈ primesUpTo N,
            ((gram N h σ)⁻¹) i j *
              (primeWeight σ p * (Real.log (p : ℝ)) ^ (j.val + i.val + 1)) := by
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, shiftedGram, moment,
        Finset.mul_sum]
    _ = ∑ i : Fin h, ∑ p ∈ primesUpTo N, ∑ j : Fin h,
          ((gram N h σ)⁻¹) i j *
            (primeWeight σ p * (Real.log (p : ℝ)) ^ (j.val + i.val + 1)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
    _ = ∑ p ∈ primesUpTo N, ∑ i : Fin h, ∑ j : Fin h,
          ((gram N h σ)⁻¹) i j *
            (primeWeight σ p * (Real.log (p : ℝ)) ^ (j.val + i.val + 1)) := by
      rw [Finset.sum_comm]
    _ = ∑ p ∈ primesUpTo N,
          primeWeight σ p * Real.log (p : ℝ) * diagonalKernel N h σ p := by
      apply Finset.sum_congr rfl
      intro p hp
      unfold diagonalKernel
      simp only [Finset.mul_sum, pow_succ, pow_add]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring

/-- Finite prime-node version of the differentiated determinant/kernel identity. -/
theorem prime_gram_logDet_kernel_hasDerivAt (N h : ℕ) (σ : ℝ)
    (hdet : (gram N h σ).det ≠ 0) :
    HasDerivAt (fun z : ℝ => Real.log ((gram N h z).det))
      (-(∑ p ∈ primesUpTo N,
        primeWeight σ p * Real.log (p : ℝ) * diagonalKernel N h σ p)) σ := by
  have htrace : (((gram N h σ)⁻¹ * (-(shiftedGram N h σ))).trace) =
      -(((gram N h σ)⁻¹ * shiftedGram N h σ).trace) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.neg_apply,
      mul_neg, Finset.sum_neg_distrib]
  have hh := finite_prime_gram_logDet_hasDerivAt N h σ hdet
  rw [htrace, trace_shifted_eq_prime_kernel_sum] at hh
  exact hh

end HVRPrimeKernelTrace
