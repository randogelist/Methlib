import HVRPrimeGramJacobiBridge
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.PosDef

/-!
Two-prime finite Gram support. This adapts the nonzero-polynomial support
step from snditeration's moment positivity to the atomic nodes log 2 and
log 3. Unlike the atomless argument, it is valid for a finite atomic measure
but only in dimension 2. It is a candidate until compiled and audited.
-/

noncomputable section
open scoped BigOperators
open Matrix

namespace HVRTwoPrimeGram

theorem evalFeature_two (c : Fin 2 → ℝ) (p : ℕ) :
    HVRPrimeAtomicGram.evalFeature c p =
      c 0 + c 1 * Real.log (p : ℝ) := by
  simp [HVRPrimeAtomicGram.evalFeature, HVRPrimeAtomicGram.feature,
    Fin.sum_univ_two]

theorem log_two_lt_log_three : Real.log (2 : ℝ) < Real.log (3 : ℝ) := by
  exact Real.log_lt_log (by norm_num) (by norm_num)

/-- Two distinct log-prime nodes detect every nonzero linear polynomial. -/
theorem exists_nonzero_prime_node (c : Fin 2 → ℝ) (hc : c ≠ 0) :
    HVRPrimeAtomicGram.evalFeature c 2 ≠ 0 ∨
      HVRPrimeAtomicGram.evalFeature c 3 ≠ 0 := by
  by_contra h
  push_neg at h
  have h2 : c 0 + c 1 * Real.log (2 : ℝ) = 0 := by
    simpa [evalFeature_two] using h.1
  have h3 : c 0 + c 1 * Real.log (3 : ℝ) = 0 := by
    simpa [evalFeature_two] using h.2
  have hprod : c 1 * (Real.log (3 : ℝ) - Real.log (2 : ℝ)) = 0 := by
    nlinarith [h2, h3]
  have hlog : Real.log (3 : ℝ) - Real.log (2 : ℝ) ≠ 0 :=
    ne_of_gt (sub_pos.mpr log_two_lt_log_three)
  have hc1 : c 1 = 0 := (mul_eq_zero.mp hprod).resolve_right hlog
  have hc0 : c 0 = 0 := by simpa only [hc1, zero_mul, add_zero] using h2
  apply hc
  funext i
  fin_cases i <;> simp [hc0, hc1]

theorem prime_two_mem {N : ℕ} (hN : 3 ≤ N) :
    2 ∈ HVRPrimeGram.primesUpTo N := by
  simp only [HVRPrimeGram.primesUpTo, Finset.mem_filter, Finset.mem_range]
  exact ⟨by omega, Nat.prime_two⟩

theorem prime_three_mem {N : ℕ} (hN : 3 ≤ N) :
    3 ∈ HVRPrimeGram.primesUpTo N := by
  simp only [HVRPrimeGram.primesUpTo, Finset.mem_filter, Finset.mem_range]
  exact ⟨by omega, Nat.prime_three⟩

/-- The witness premise is discharged for cutoff at least 3 and dimension 2. -/
theorem quadratic_pos (N : ℕ) (sigma : ℝ) (hN : 3 ≤ N)
    (c : Fin 2 → ℝ) (hc : c ≠ 0) :
    0 < ∑ i : Fin 2, ∑ j : Fin 2,
      c i * HVRPrimeMomentJacobi.gram N 2 sigma i j * c j := by
  rcases exists_nonzero_prime_node c hc with h2 | h3
  · exact HVRPrimeGramJacobiBridge.primeMomentGram_quadratic_pos_of_prime_witness
      N 2 sigma c (prime_two_mem hN) h2
  · exact HVRPrimeGramJacobiBridge.primeMomentGram_quadratic_pos_of_prime_witness
      N 2 sigma c (prime_three_mem hN) h3

/-- Actual finite prime moment matrix is positive definite in dimension two. -/
theorem gram_posDef (N : ℕ) (sigma : ℝ) (hN : 3 ≤ N) :
    (HVRPrimeMomentJacobi.gram N 2 sigma).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · ext i j
    simp [HVRPrimeMomentJacobi.gram, Nat.add_comm]
  · intro c hc
    simpa only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial,
      Finset.mul_sum, mul_assoc] using quadratic_pos N sigma hN c hc

theorem gram_det_pos (N : ℕ) (sigma : ℝ) (hN : 3 ≤ N) :
    0 < (HVRPrimeMomentJacobi.gram N 2 sigma).det :=
  (gram_posDef N sigma hN).det_pos

/-- Prime-specific Jacobi formula with the determinant obligation discharged. -/
theorem gram_logDet_hasDerivAt (N : ℕ) (sigma : ℝ) (hN : 3 ≤ N) :
    HasDerivAt
      (fun z : ℝ => Real.log ((HVRPrimeMomentJacobi.gram N 2 z).det))
      (((HVRPrimeMomentJacobi.gram N 2 sigma)⁻¹ *
        (-(HVRPrimeMomentJacobi.shiftedGram N 2 sigma))).trace) sigma :=
  HVRPrimeMomentJacobi.finite_prime_gram_logDet_hasDerivAt N 2 sigma
    (ne_of_gt (gram_det_pos N sigma hN))

end HVRTwoPrimeGram
