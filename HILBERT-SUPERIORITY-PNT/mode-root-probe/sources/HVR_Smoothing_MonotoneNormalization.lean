import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

noncomputable section

/-!
Pointwise input for the one-sided smoothing argument. A monotone mass A is
normalized by exp(-t). The applications to the actual prime counting mass,
integration against a kernel, and the Fourier limit are not asserted here.
-/
namespace HVRMonotoneNormalization

/-- Extend a mass by zero on the negative half-line. -/
def cutoffMass (A : ℝ → ℝ) (t : ℝ) : ℝ :=
  if 0 ≤ t then A t else 0

/-- A nonnegative-at-zero monotone mass stays monotone after zero extension. -/
theorem cutoffMass_monotone (A : ℝ → ℝ) (hA : Monotone A)
    (h0 : 0 ≤ A 0) : Monotone (cutoffMass A) := by
  intro x y hxy
  by_cases hx : 0 ≤ x
  · have hy : 0 ≤ y := le_trans hx hxy
    simpa [cutoffMass, hx, hy] using hA hxy
  · by_cases hy : 0 ≤ y
    · have hAy : 0 ≤ A y := le_trans h0 (hA hy)
      simpa [cutoffMass, hx, hy] using hAy
    · simp [cutoffMass, hx, hy]

/-- Exponential normalization of a mass in logarithmic coordinates. -/
def normalizedMass (A : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (-t) * A t

/-- Monotonicity of the underlying mass supplies the pointwise one-sided
comparison used inside the smoothing integrals. -/
theorem normalizedMass_le (A : ℝ → ℝ) (hA : Monotone A)
    {x y : ℝ} (hxy : x ≤ y) :
    normalizedMass A x ≤ Real.exp (y - x) * normalizedMass A y := by
  have hex : Real.exp (-x) = Real.exp (y - x) * Real.exp (-y) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h1 := mul_le_mul_of_nonneg_left (hA hxy) (le_of_lt (Real.exp_pos (-y)))
  have h2 := mul_le_mul_of_nonneg_left h1 (le_of_lt (Real.exp_pos (y - x)))
  unfold normalizedMass
  rw [hex]
  simpa only [mul_assoc] using h2

/-- The same comparison holds for the zero-extended mass used on the whole
real line in smoothing. -/
theorem normalized_cutoffMass_le (A : ℝ → ℝ) (hA : Monotone A)
    (h0 : 0 ≤ A 0) {x y : ℝ} (hxy : x ≤ y) :
    normalizedMass (cutoffMass A) x ≤
      Real.exp (y - x) * normalizedMass (cutoffMass A) y :=
  normalizedMass_le (cutoffMass A) (cutoffMass_monotone A hA h0) hxy

/-- Nonnegative kernel weights preserve the pointwise comparison. -/
theorem weighted_normalized_cutoffMass_le (A : ℝ → ℝ) (hA : Monotone A)
    (h0 : 0 ≤ A 0) {x y k : ℝ} (hxy : x ≤ y) (hk : 0 ≤ k) :
    k * normalizedMass (cutoffMass A) x ≤
      k * (Real.exp (y - x) * normalizedMass (cutoffMass A) y) :=
  mul_le_mul_of_nonneg_left (normalized_cutoffMass_le A hA h0 hxy) hk

end HVRMonotoneNormalization
