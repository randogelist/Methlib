import Mathlib.NumberTheory.AbelSummation
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Tactic

/-!
Candidate finite Abel-summation bridge for the actual prime-log coefficient.

No Lean compiler or axiom audit was run locally for this source.  It does not
invoke `LSeries_eq_mul_integral`.  It DOES invoke Mathlib's more general finite
Abel summation theorem `sum_mul_eq_sub_integral_mul₀'`, and it uses Mathlib's
complex-power derivative theorem.  Dependency tracing is needed before any
independence claim.  These are finite identities, not the required infinite
Mellin identity.  Passing to infinity, showing the boundary term vanishes,
and matching to the project's complex L-series remain separate obligations.
-/

noncomputable section

open Finset MeasureTheory

namespace HVRNativeMellinAbel

/-- The logarithmic prime coefficient, zero away from primes. -/
def primeCoefficientC (n : ℕ) : ℂ :=
  if Nat.Prime n then (Real.log (n : ℝ) : ℂ) else 0

theorem primeCoefficientC_zero : primeCoefficientC 0 = 0 := by
  simp [primeCoefficientC]

/-- The finite prime-log partial sum. -/
def primeMass (n : ℕ) : ℂ := ∑ k ∈ Finset.Icc 0 n, primeCoefficientC k

/-- Finite prime-weight Abel summation.  Smoothness and derivative
integrability on the finite interval are explicit hypotheses. -/
theorem finite_prime_abel (f : ℝ → ℂ) (N : ℕ)
    (hf_diff : ∀ t ∈ Set.Icc (1 : ℝ) N, DifferentiableAt ℝ f t)
    (hf_int : IntegrableOn (deriv f) (Set.Icc (1 : ℝ) N)) :
    (∑ k ∈ Finset.Icc 0 N, f k * primeCoefficientC k) =
      f N * primeMass N -
        ∫ t in Set.Ioc (1 : ℝ) N, deriv f t * primeMass ⌊t⌋₊ := by
  simpa only [primeMass] using
    (sum_mul_eq_sub_integral_mul₀' primeCoefficientC primeCoefficientC_zero N
      hf_diff hf_int)

/-- Complex-power specialization of finite prime-weight Abel summation.
The derivative and integrability assumptions are retained explicitly; no
infinite limiting operation is asserted. -/
theorem finite_prime_mellin_abel (s : ℂ) (hs : s ≠ 0) (N : ℕ)
    (hf_diff : ∀ t ∈ Set.Icc (1 : ℝ) N,
      DifferentiableAt ℝ (fun x : ℝ => (x : ℂ) ^ (-s)) t)
    (hf_int : IntegrableOn (deriv (fun x : ℝ => (x : ℂ) ^ (-s)))
      (Set.Icc (1 : ℝ) N)) :
    (∑ k ∈ Finset.Icc 0 N, (k : ℂ) ^ (-s) * primeCoefficientC k) =
      (N : ℂ) ^ (-s) * primeMass N -
        ∫ t in Set.Ioc (1 : ℝ) N,
          ((-s) * (t : ℂ) ^ (-s - 1)) * primeMass ⌊t⌋₊ := by
  calc
    (∑ k ∈ Finset.Icc 0 N, (k : ℂ) ^ (-s) * primeCoefficientC k) =
        (N : ℂ) ^ (-s) * primeMass N -
          ∫ t in Set.Ioc (1 : ℝ) N,
            deriv (fun x : ℝ => (x : ℂ) ^ (-s)) t * primeMass ⌊t⌋₊ :=
      by simpa only [Complex.ofReal_natCast] using
        (finite_prime_abel (fun x : ℝ => (x : ℂ) ^ (-s)) N hf_diff hf_int)
    _ = (N : ℂ) ^ (-s) * primeMass N -
          ∫ t in Set.Ioc (1 : ℝ) N,
            ((-s) * (t : ℂ) ^ (-s - 1)) * primeMass ⌊t⌋₊ := by
      congr 1
      apply setIntegral_congr_fun measurableSet_Ioc
      intro t ht
      change deriv (fun x : ℝ => (x : ℂ) ^ (-s)) t * primeMass ⌊t⌋₊ =
        ((-s) * (t : ℂ) ^ (-s - 1)) * primeMass ⌊t⌋₊
      rw [Complex.deriv_ofReal_cpow_const (ne_of_gt (lt_trans zero_lt_one ht.1))
        (neg_ne_zero.mpr hs)]

end HVRNativeMellinAbel
