import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

/-!
Candidate restricted separation identities for HVR smoothing.

No Lean compiler or named axiom audit has been run on this source.  Neither
declaration invokes `MeasureTheory.integral_integral_swap`, general Fubini, or
Tonelli.  The proofs use the ordinary one-variable identities for multiplying
a Bochner integral by a constant; their upstream dependencies still require
inspection.  The density below is an abstract complex-valued function.

The separable statement applies only to products f(u)g(t).  The single-frequency statement performs the u-integration at a FIXED frequency
for an abstract density, not specifically the prime density.
The actual smoothing integrand has the coupled phase exp(-i*t*u), so these
statements do NOT justify interchanging its two continuous integrals.  An
approximation/limit theorem and suitable integrability bounds remain open.
-/

noncomputable section

open MeasureTheory

namespace HVRNativeFubini

/-- Swapping iterated integrals for a genuinely separable scalar integrand. -/
theorem separable_integral_swap (A B : Set ℝ) (f g : ℝ → ℂ) :
    (∫ u : ℝ in A, ∫ t : ℝ in B, f u * g t) =
      ∫ t : ℝ in B, ∫ u : ℝ in A, f u * g t := by
  simp only [integral_const_mul, integral_mul_const]

/-- Abstract density-error Laplace integral over the positive half-line. -/
def densityLaplace (rho : ℝ → ℂ) (z : ℂ) : ℂ :=
  ∫ u : ℝ in Set.Ioi 0, (rho u - 1) * Complex.exp (-z * (u : ℂ))

/-- Mixed integrand for an abstract density at one fixed frequency. -/
def fixedFrequencyMixed (rho : ℝ → ℂ) (psi : ℂ) (a x t u : ℝ) : ℂ :=
  ((rho u - 1) * Complex.exp (-(a : ℂ) * (u : ℂ))) *
    (psi * Complex.exp ((t : ℂ) * Complex.I * ((x - u : ℝ) : ℂ)))

theorem fixed_frequency_factorization (rho : ℝ → ℂ) (psi : ℂ) (a x t u : ℝ) :
    fixedFrequencyMixed rho psi a x t u =
      (psi * Complex.exp ((t : ℂ) * Complex.I * (x : ℂ))) *
        ((rho u - 1) *
          Complex.exp (-((a : ℂ) + (t : ℂ) * Complex.I) * (u : ℂ))) := by
  have hexp : Complex.exp (-(a : ℂ) * (u : ℂ)) *
      Complex.exp ((t : ℂ) * Complex.I * ((x - u : ℝ) : ℂ)) =
      Complex.exp ((t : ℂ) * Complex.I * (x : ℂ)) *
        Complex.exp (-((a : ℂ) + (t : ℂ) * Complex.I) * (u : ℂ)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  unfold fixedFrequencyMixed
  calc
    ((rho u - 1) * Complex.exp (-(a : ℂ) * (u : ℂ))) *
        (psi * Complex.exp ((t : ℂ) * Complex.I * ((x - u : ℝ) : ℂ))) =
      psi * ((rho u - 1) *
        (Complex.exp (-(a : ℂ) * (u : ℂ)) *
          Complex.exp ((t : ℂ) * Complex.I * ((x - u : ℝ) : ℂ)))) := by ring
    _ = (psi * Complex.exp ((t : ℂ) * Complex.I * (x : ℂ))) *
        ((rho u - 1) *
          Complex.exp (-((a : ℂ) + (t : ℂ) * Complex.I) * (u : ℂ))) := by
      rw [hexp]
      ring

/-- The abstract density-error Laplace identity at one fixed frequency. -/
theorem fixed_frequency_laplace (rho : ℝ → ℂ) (psi : ℂ) (a x t : ℝ) :
    (∫ u : ℝ in Set.Ioi 0, fixedFrequencyMixed rho psi a x t u) =
      (psi * Complex.exp ((t : ℂ) * Complex.I * (x : ℂ))) *
        densityLaplace rho ((a : ℂ) + (t : ℂ) * Complex.I) := by
  simp_rw [fixed_frequency_factorization]
  rw [integral_const_mul] <;> simp only [densityLaplace]

end HVRNativeFubini
