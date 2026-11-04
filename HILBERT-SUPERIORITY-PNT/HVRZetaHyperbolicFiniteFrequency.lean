import HVR_PrimeDensity_FubiniBridge
import NativeFubini

/-!
Finite-frequency adapter from the audited HVRNativeFubini separable route to
the actual HVR prime-density Laplace transform.

This module treats finitely many frequencies. It does not establish the
continuous-frequency interchange used by the PNT root: a finite-frequency
approximation and both limiting passages remain to be supplied and audited.
The prime-mode integrability proof uses the existing actual prime-density
integrability theorem, not the product-integrability theorem.

Candidate only: no local Lean compiler or new theorem-level audit was run.
-/

noncomputable section
open Filter MeasureTheory
open scoped Topology
open HVRPrimeLogDensity HVRPrimeZetaSplit HVRPrimeDensityLaplace
open HVRPrimeDensityFubiniBridge

namespace HVRZetaHyperbolicFiniteFrequency

/-- The HVRNativeFubini fixed-frequency identity for the actual prime density. -/
theorem actual_fixed_frequency (ψ : ℝ → ℂ) (a x t : ℝ) :
    (∫ u : ℝ in Set.Ioi 0, mixed ψ a x u t) =
      (ψ t * Complex.exp ((t : ℂ) * Complex.I * (x : ℂ))) *
        primeDensityLaplace ((a : ℂ) + (t : ℂ) * Complex.I) := by
  have h := HVRNativeFubini.fixed_frequency_laplace
    (fun u : ℝ => (logPrimeDensity u : ℂ)) (ψ t) a x t
  simpa only [HVRNativeFubini.fixedFrequencyMixed, HVRNativeFubini.densityLaplace,
    mixed, dampedError, primeDensityLaplace] using h

/-- Every fixed-frequency mode is integrable for positive Abel damping. -/
theorem actual_fixed_frequency_integrable
    (ψ : ℝ → ℂ) (a x t : ℝ) (ha : 0 < a) :
    IntegrableOn (fun u : ℝ => mixed ψ a x u t) (Set.Ioi 0) volume := by
  have hs : 1 < 1 + a := by linarith
  have h := primeDensity_integrable (1 + a) t hs
  have hp : zetaPoint (1 + a) t - 1 =
      (a : ℂ) + (t : ℂ) * Complex.I := by
    simp only [zetaPoint, Complex.ofReal_add, Complex.ofReal_one]
    ring
  rw [hp] at h
  have hfun : (fun u : ℝ => mixed ψ a x u t) =
      (fun u : ℝ =>
        (ψ t * Complex.exp ((t : ℂ) * Complex.I * (x : ℂ))) *
          (((logPrimeDensity u : ℂ) - 1) *
            Complex.exp (-((a : ℂ) + (t : ℂ) * Complex.I) * (u : ℂ)))) := by
    funext u
    exact mixed_factorization ψ a x u t
  rw [hfun]
  exact h.const_mul _

/-- Exact finite-frequency identity for the actual damped prime error.

There is no convergence premise on the test at individual frequencies.
This theorem does not replace integration over a continuum of frequencies.
-/
theorem actual_finite_frequency_identity
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (frequency : ι → ℝ)
    (coefficient : ι → ℂ) (ψ : ℝ → ℂ) (a x : ℝ) (ha : 0 < a) :
    (∫ u : ℝ in Set.Ioi 0,
      ∑ i ∈ S, coefficient i * mixed ψ a x u (frequency i)) =
    ∑ i ∈ S, coefficient i *
      ((ψ (frequency i) *
        Complex.exp (((frequency i : ℝ) : ℂ) * Complex.I * (x : ℂ))) *
        primeDensityLaplace
          ((a : ℂ) + ((frequency i : ℝ) : ℂ) * Complex.I)) := by
  rw [integral_finsetSum S
    (fun i _ => (actual_fixed_frequency_integrable ψ a x (frequency i) ha).const_mul
      (coefficient i))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_const_mul, actual_fixed_frequency]

/-- Conditional bridge to the exact continuous-frequency identity.

The two hypotheses are precisely the separate convergence obligations for a
sequence of finite-frequency approximations. They are not discharged here;
in particular no compact-support quadrature or general Fubini theorem follows
from this statement alone.
-/
theorem actual_continuous_identity_of_frequency_approximation
    (ψ : ℝ → ℂ) (a x : ℝ) (ha : 0 < a)
    (frequency : ℕ → ℕ → ℝ) (coefficient : ℕ → ℕ → ℂ)
    (hleft : Tendsto
      (fun N : ℕ => ∫ u : ℝ in Set.Ioi 0,
        ∑ i ∈ Finset.range N, coefficient N i * mixed ψ a x u (frequency N i))
      atTop (𝓝 (∫ u : ℝ in Set.Ioi 0, dampedError a u * kernel ψ (x - u))))
    (hright : Tendsto
      (fun N : ℕ => ∑ i ∈ Finset.range N, coefficient N i *
        ((ψ (frequency N i) *
          Complex.exp (((frequency N i : ℝ) : ℂ) * Complex.I * (x : ℂ))) *
          primeDensityLaplace
            ((a : ℂ) + ((frequency N i : ℝ) : ℂ) * Complex.I)))
      atTop (𝓝 (∫ t : ℝ,
        (ψ t * Complex.exp ((t : ℂ) * Complex.I * (x : ℂ))) *
          primeDensityLaplace ((a : ℂ) + (t : ℂ) * Complex.I)))) :
    (∫ u : ℝ in Set.Ioi 0, dampedError a u * kernel ψ (x - u)) =
      ∫ t : ℝ, (ψ t * Complex.exp ((t : ℂ) * Complex.I * (x : ℂ))) *
        primeDensityLaplace ((a : ℂ) + (t : ℂ) * Complex.I) := by
  have heq : (fun N : ℕ => ∫ u : ℝ in Set.Ioi 0,
      ∑ i ∈ Finset.range N, coefficient N i * mixed ψ a x u (frequency N i)) =
      (fun N : ℕ => ∑ i ∈ Finset.range N, coefficient N i *
        ((ψ (frequency N i) *
          Complex.exp (((frequency N i : ℝ) : ℂ) * Complex.I * (x : ℂ))) *
          primeDensityLaplace
            ((a : ℂ) + ((frequency N i : ℝ) : ℂ) * Complex.I))) := by
    funext N
    exact actual_finite_frequency_identity (Finset.range N) (frequency N)
      (coefficient N) ψ a x ha
  rw [heq] at hleft
  exact tendsto_nhds_unique hleft hright

end HVRZetaHyperbolicFiniteFrequency

