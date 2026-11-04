import HVR_Prime_Gram
import HVR_ZetaHyperMatrixJacobi

/-!
Finite prime-moment matrices on the exact prime weights already used by the
PNT project's HVR_Prime_Gram module.  The generic finite matrix log-determinant
calculus is adapted from the Zetahyperbolic Jacobi chain; see the accompanying
port modules for provenance.

The all-dimensional matrix endpoint has the explicit determinant-nonzero
assumption.  The one-dimensional log-prime-mass endpoint discharges its
nonzero premise when the finite cutoff includes 2.  No infinite moment,
zeta log-derivative, half-plane continuation, or PNT endpoint is claimed.
This source is a candidate pending external cached RC1 compilation and audit.
-/

noncomputable section
open scoped BigOperators Topology
open Matrix

namespace HVRPrimeMomentJacobi

open HVRPrimeGram

/-- The finite prime moment, with the original HVR prime-spectral weight. -/
def moment (N : ℕ) (σ : ℝ) (k : ℕ) : ℝ :=
  ∑ p ∈ primesUpTo N,
    primeWeight σ p * (Real.log (p : ℝ)) ^ k

/-- The proposed finite Hankel matrix of prime moments. -/
def gram (N h : ℕ) (σ : ℝ) : Matrix (Fin h) (Fin h) ℝ :=
  fun i j => moment N σ (i.val + j.val)

/-- Its once-shifted moment matrix. -/
def shiftedGram (N h : ℕ) (σ : ℝ) : Matrix (Fin h) (Fin h) ℝ :=
  fun i j => moment N σ (i.val + j.val + 1)

theorem moment_zero_eq_primeMass (N : ℕ) (σ : ℝ) :
    moment N σ 0 = HVRPrimeGram.primeMass N σ := by
  simp [moment, HVRPrimeGram.primeMass]

/-- Each finite moment differentiates to minus the next moment. -/
theorem moment_hasDerivAt (N : ℕ) (σ : ℝ) (k : ℕ) :
    HasDerivAt (fun z : ℝ => moment N z k) (-(moment N σ (k + 1))) σ := by
  have hterm (p : ℕ) :
      HasDerivAt
        (fun z : ℝ => primeWeight z p * (Real.log (p : ℝ)) ^ k)
        (-(primeWeight σ p * (Real.log (p : ℝ)) ^ (k + 1))) σ := by
    have harg : HasDerivAt (fun z : ℝ => -(z * Real.log (p : ℝ)))
        (-(Real.log (p : ℝ))) σ := by
      have hfun : (fun z : ℝ => -(z * Real.log (p : ℝ))) =
          (fun z : ℝ => z * (-(Real.log (p : ℝ)))) := by
        funext z
        ring
      rw [hfun]
      simpa [id] using
        (hasDerivAt_id σ).mul_const (-(Real.log (p : ℝ)))
    have hexp := (Real.hasDerivAt_exp (-(σ * Real.log (p : ℝ)))).comp σ harg
    have hprod := (hexp.const_mul (Real.log (p : ℝ))).mul_const
      ((Real.log (p : ℝ)) ^ k)
    have hcoeff :
        Real.log (p : ℝ) *
          (Real.exp (-(σ * Real.log (p : ℝ))) * -(Real.log (p : ℝ))) *
            (Real.log (p : ℝ)) ^ k =
        -(primeWeight σ p * (Real.log (p : ℝ)) ^ (k + 1)) := by
      simp only [primeWeight, pow_succ]
      ring
    rw [hcoeff] at hprod
    simpa only [primeWeight, Function.comp_apply, neg_mul] using hprod
  have hsum := HasDerivAt.fun_sum (u := primesUpTo N) (fun p _ => hterm p)
  simpa only [moment, Finset.sum_neg_distrib] using hsum

/-- The prime moment matrix is an actual differentiable finite matrix curve. -/
theorem gram_entry_hasDerivAt (N h : ℕ) (σ : ℝ) (i j : Fin h) :
    HasDerivAt (fun z : ℝ => gram N h z i j)
      (-(shiftedGram N h σ i j)) σ := by
  simpa only [gram, shiftedGram] using
    moment_hasDerivAt N σ (i.val + j.val)

/-- Finite prime Gram Jacobi formula with the determinant premise explicit. -/
theorem finite_prime_gram_logDet_hasDerivAt (N h : ℕ) (σ : ℝ)
    (hdet : (gram N h σ).det ≠ 0) :
    HasDerivAt (fun z : ℝ => Real.log ((gram N h z).det))
      (((gram N h σ)⁻¹ * (-(shiftedGram N h σ))).trace) σ := by
  apply ManuscriptChain.MatrixCurveJacobi.generic_logDet_hasDerivAt
  · intro i j
    simpa only [Matrix.neg_apply] using gram_entry_hasDerivAt N h σ i j
  · exact hdet

/-- If the cutoff contains 2, the original prime mass is strictly positive. -/
theorem primeMass_pos (N : ℕ) (σ : ℝ) (hN : 2 ≤ N) :
    0 < HVRPrimeGram.primeMass N σ := by
  have hmem : 2 ∈ primesUpTo N := by
    simp only [primesUpTo, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, Nat.prime_two⟩
  have hweight : 0 < primeWeight σ 2 := by
    unfold primeWeight
    exact mul_pos (Real.log_pos (by norm_num)) (Real.exp_pos _)
  have hle : primeWeight σ 2 ≤ HVRPrimeGram.primeMass N σ := by
    unfold HVRPrimeGram.primeMass
    apply Finset.single_le_sum
    · intro p hp
      exact primeWeight_nonneg σ (Finset.mem_filter.mp hp).2
    · exact hmem
  exact lt_of_lt_of_le hweight hle

/-- Premise-free Jacobi specialization except for the explicit cutoff bound. -/
theorem log_primeMass_hasDerivAt (N : ℕ) (σ : ℝ) (hN : 2 ≤ N) :
    HasDerivAt (fun z : ℝ => Real.log (HVRPrimeGram.primeMass N z))
      (-(moment N σ 1) / HVRPrimeGram.primeMass N σ) σ := by
  have hm : moment N σ 0 ≠ 0 := by
    rw [moment_zero_eq_primeMass]
    exact ne_of_gt (primeMass_pos N σ hN)
  have hh := (moment_hasDerivAt N σ 0).log hm
  simpa only [zero_add, moment_zero_eq_primeMass] using hh

end HVRPrimeMomentJacobi
