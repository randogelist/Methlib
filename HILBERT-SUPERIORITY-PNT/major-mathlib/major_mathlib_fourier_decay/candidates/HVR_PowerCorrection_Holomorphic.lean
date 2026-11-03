import HVR_Prime_PowerCorrection
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.Trigonometric

open scoped BigOperators

noncomputable section

/-!
Conditional Weierstrass bridge for the actual geometrically resummed complex
prime-power correction.  Termwise differentiability and the uniform bound by
the audited real correction are explicit hypotheses.  This does not establish
the hypotheses, the zeta identity, boundary zero-freeness, or PNT.
-/
namespace HVRPowerCorrectionHolomorphic

open HVRPrimePowerCorrection

/-- The entire exponential ratio p^(-z), represented without a branch cut. -/
def complexRatio (n : ℕ) (z : ℂ) : ℂ :=
  Complex.exp (-z * (Real.log (n : ℝ) : ℂ))

/-- Geometrically resummed prime-power correction term; zero off primes. -/
def complexCorrectionTerm (n : ℕ) (z : ℂ) : ℂ :=
  if Nat.Prime n then
    (Real.log (n : ℝ) : ℂ) * (complexRatio n z) ^ 2 / (1 - complexRatio n z)
  else 0

/-- Complex sum, interpreted as a convergent series only where summability
has been established. -/
def complexCorrection (z : ℂ) : ℂ :=
  ∑' n : ℕ, complexCorrectionTerm n z

/-- An open strict right half-plane. -/
def halfPlane (a : ℝ) : Set ℂ := {z | a < z.re}

theorem halfPlane_isOpen (a : ℝ) : IsOpen (halfPlane a) := by
  simpa only [halfPlane] using isOpen_lt continuous_const Complex.continuous_re

/-- A concrete pointwise majorant implies actual absolute summability. -/
theorem complexCorrection_summable_of_bound
    (a : ℝ) (ha : (1 / 2 : ℝ) < a) (z : ℂ)
    (hbound : ∀ n, ‖complexCorrectionTerm n z‖ ≤ correctionTerm a n) :
    Summable (fun n => complexCorrectionTerm n z) := by
  exact Summable.of_norm_bounded (correction_summable a ha) hbound

/-- Weierstrass bridge: the real summable correction provides the majorant;
termwise holomorphicity and the precise uniform domination remain hypotheses. -/
theorem complexCorrection_differentiableOn_of_bounds
    (a : ℝ) (ha : (1 / 2 : ℝ) < a)
    (hterm : ∀ n, DifferentiableOn ℂ (complexCorrectionTerm n) (halfPlane a))
    (hbound : ∀ n z, z ∈ halfPlane a →
      ‖complexCorrectionTerm n z‖ ≤ correctionTerm a n) :
    DifferentiableOn ℂ complexCorrection (halfPlane a) := by
  change DifferentiableOn ℂ (fun z : ℂ => ∑' n : ℕ, complexCorrectionTerm n z)
    (halfPlane a)
  exact Complex.differentiableOn_tsum_of_summable_norm
    (correction_summable a ha) hterm (halfPlane_isOpen a) hbound

end HVRPowerCorrectionHolomorphic
