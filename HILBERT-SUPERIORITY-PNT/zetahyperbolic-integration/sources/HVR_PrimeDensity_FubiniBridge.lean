import HVR_PrimeDensity_Laplace
import Mathlib.MeasureTheory.Integral.Prod

noncomputable section
open MeasureTheory HVRPrimeLogDensity HVRPrimeDensityLaplace

/-! Candidate exact Fubini bridge for the actual prime-count error.
The product-integrability premise is explicit and remains to be discharged.
The frequency test defines a kernel directly; this module does not prove
positivity, normalization, compact Fourier support, Fourier decay, or PNT.
No local Lean execution was performed. -/
namespace HVRPrimeDensityFubiniBridge

/-- A kernel defined by an ordinary-frequency inverse integral. -/
def kernel (ψ : ℝ → ℂ) (y : ℝ) : ℂ :=
  ∫ t : ℝ, ψ t * Complex.exp ((t : ℂ) * Complex.I * (y : ℂ))

/-- The actual prime-count error with Abel damping. -/
def dampedError (a u : ℝ) : ℂ :=
  ((logPrimeDensity u : ℂ) - 1) * Complex.exp (-(a : ℂ) * (u : ℂ))

/-- The mixed integrand whose product integrability justifies Fubini. -/
def mixed (ψ : ℝ → ℂ) (a x u t : ℝ) : ℂ :=
  dampedError a u *
    (ψ t * Complex.exp ((t : ℂ) * Complex.I * ((x - u : ℝ) : ℂ)))

/-- Algebraic separation of spatial and Laplace-frequency factors. -/
theorem mixed_factorization (ψ : ℝ → ℂ) (a x u t : ℝ) :
    mixed ψ a x u t =
      (ψ t * Complex.exp ((t : ℂ) * Complex.I * (x : ℂ))) *
        (((logPrimeDensity u : ℂ) - 1) *
          Complex.exp (-((a : ℂ) + (t : ℂ) * Complex.I) * (u : ℂ))) := by
  have hexp : Complex.exp (-(a : ℂ) * (u : ℂ)) *
      Complex.exp ((t : ℂ) * Complex.I * ((x - u : ℝ) : ℂ)) =
      Complex.exp ((t : ℂ) * Complex.I * (x : ℂ)) *
        Complex.exp (-((a : ℂ) + (t : ℂ) * Complex.I) * (u : ℂ)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  unfold mixed dampedError
  calc
    (((logPrimeDensity u : ℂ) - 1) * Complex.exp (-(a : ℂ) * (u : ℂ))) *
        (ψ t * Complex.exp ((t : ℂ) * Complex.I * ((x - u : ℝ) : ℂ))) =
      ψ t * (((logPrimeDensity u : ℂ) - 1) *
        (Complex.exp (-(a : ℂ) * (u : ℂ)) *
          Complex.exp ((t : ℂ) * Complex.I * ((x - u : ℝ) : ℂ)))) := by ring
    _ = _ := by rw [hexp]; ring

/-- Fubini identifies the Abel-smoothed actual prime error with the integral
of its actual Laplace transform. Product integrability is an explicit input. -/
theorem abel_smoothing_eq_frequency_integral (ψ : ℝ → ℂ) (a x : ℝ)
    (hpair : Integrable (fun p : ℝ × ℝ => mixed ψ a x p.1 p.2)
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume)) :
    (∫ u : ℝ in Set.Ioi 0, dampedError a u * kernel ψ (x - u)) =
      ∫ t : ℝ, (ψ t * Complex.exp ((t : ℂ) * Complex.I * (x : ℂ))) *
        primeDensityLaplace ((a : ℂ) + (t : ℂ) * Complex.I) := by
  calc
    (∫ u : ℝ in Set.Ioi 0, dampedError a u * kernel ψ (x - u)) =
        ∫ u : ℝ in Set.Ioi 0, ∫ t : ℝ, mixed ψ a x u t := by
      apply integral_congr_ae
      filter_upwards [] with u
      unfold kernel mixed
      rw [integral_const_mul]
    _ = ∫ t : ℝ, ∫ u : ℝ in Set.Ioi 0, mixed ψ a x u t := by
      exact integral_integral_swap hpair
    _ = ∫ t : ℝ, (ψ t * Complex.exp ((t : ℂ) * Complex.I * (x : ℂ))) *
        primeDensityLaplace ((a : ℂ) + (t : ℂ) * Complex.I) := by
      apply integral_congr_ae
      filter_upwards [] with t
      simp_rw [mixed_factorization]
      rw [integral_const_mul]
      rfl

end HVRPrimeDensityFubiniBridge
