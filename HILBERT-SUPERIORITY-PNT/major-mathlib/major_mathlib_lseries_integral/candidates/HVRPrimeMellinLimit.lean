import NativeMellinAbel

/-!
Conditional infinite prime-weight Mellin bridge, derived from the finite
Abel identity. It does not invoke `LSeries_eq_mul_integral`. The finite
partial sums, boundary term and truncated integrals must be proved to have
the indicated limits before this yields an unconditional prime Mellin bridge.
The finite identity itself retains Mathlib's general Abel summation theorem.
-/

noncomputable section

open Finset Filter MeasureTheory

namespace HVRPrimeMellinLimit

open HVRNativeMellinAbel

def primePartial (s : ℂ) (N : ℕ) : ℂ :=
  ∑ k ∈ Finset.Icc 0 N, (k : ℂ) ^ (-s) * primeCoefficientC k

def boundaryTerm (s : ℂ) (N : ℕ) : ℂ :=
  (N : ℂ) ^ (-s) * primeMass N

def truncatedDerivativeIntegral (s : ℂ) (N : ℕ) : ℂ :=
  ∫ t in Set.Ioc (1 : ℝ) N,
    ((-s) * (t : ℂ) ^ (-s - 1)) * primeMass ⌊t⌋₊

/-- Limit transfer; all convergence and finite regularity inputs are explicit. -/
theorem prime_mellin_of_finite_abel_limits (s : ℂ) (hs : s ≠ 0)
    (L I : ℂ)
    (hf_diff : ∀ N : ℕ, ∀ t ∈ Set.Icc (1 : ℝ) N,
      DifferentiableAt ℝ (fun x : ℝ => (x : ℂ) ^ (-s)) t)
    (hf_int : ∀ N : ℕ, IntegrableOn
      (deriv (fun x : ℝ => (x : ℂ) ^ (-s))) (Set.Icc (1 : ℝ) N))
    (hseries : Tendsto (primePartial s) atTop (𝓝 L))
    (hboundary : Tendsto (boundaryTerm s) atTop (𝓝 0))
    (hintegral : Tendsto (truncatedDerivativeIntegral s) atTop (𝓝 I)) :
    L = -I := by
  have hfinite : primePartial s = fun N =>
      boundaryTerm s N - truncatedDerivativeIntegral s N := by
    funext N
    exact finite_prime_mellin_abel s hs N (hf_diff N) (hf_int N)
  have hlimit : Tendsto (primePartial s) atTop (𝓝 (0 - I)) := by
    rw [hfinite]
    exact hboundary.sub hintegral
  have hEq : L = 0 - I := tendsto_nhds_unique hseries hlimit
  simpa only [zero_sub] using hEq

end HVRPrimeMellinLimit
