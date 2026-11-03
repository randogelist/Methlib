import HVR_PhysicalKernel_WindowAlgebra

noncomputable section
open MeasureTheory
open HVRPhysicalKernelWindowAlgebra

/-!
Candidate explicit choice of the positive window used by the prime-density
squeeze. This proves only the numerical window conditions from a stated tail
bound. It does not construct a concentrated kernel, prove its Fourier support,
or prove the two smoothing limits. No Lean was executed locally.
-/
namespace HVRPhysicalKernelCanonicalWindow

def canonicalWindow (δ : ℝ) : ℝ := Real.log (1 + δ / 2)

theorem canonicalWindow_pos (δ : ℝ) (hδ : 0 < δ) :
    0 < canonicalWindow δ := by
  unfold canonicalWindow
  apply Real.log_pos
  linarith

theorem canonicalWindow_exp (δ : ℝ) (hδ : 0 < δ) :
    Real.exp (canonicalWindow δ) = 1 + δ / 2 := by
  unfold canonicalWindow
  apply Real.exp_log
  linarith

/-- An explicit short window suffices whenever its complement has at most
half-delta mass. Tail concentration and kernel existence are separate. -/
theorem canonicalWindow_bounds_of_tail (δ : ℝ) (hδ : 0 < δ)
    (k : ℝ → ℝ) (hk : ∀ x, 0 ≤ k x)
    (hki : IntegrableOn k Set.univ volume)
    (hmass : (∫ x : ℝ in Set.univ, k x) = 1)
    (htail : (∫ x : ℝ in (Set.Icc 0 (canonicalWindow δ))ᶜ, k x) ≤ δ / 2) :
    (1 - δ) * Real.exp (canonicalWindow δ) ≤
        (∫ x : ℝ in Set.Icc 0 (canonicalWindow δ), k x) ∧
    Real.exp (canonicalWindow δ) *
        (∫ x : ℝ in Set.Icc 0 (canonicalWindow δ), k x) ≤ 1 + δ ∧
    (∫ x : ℝ in (Set.Icc 0 (canonicalWindow δ))ᶜ, k x) ≤ δ := by
  have he := canonicalWindow_exp δ hδ
  have hexp : Real.exp (canonicalWindow δ) ≤ 1 + δ := by
    rw [he]
    linarith
  have ht : (∫ x : ℝ in (Set.Icc 0 (canonicalWindow δ))ᶜ, k x) ≤ δ := by
    linarith
  have ht' : (∫ x : ℝ in (Set.Icc 0 (canonicalWindow δ))ᶜ, k x) ≤
      1 - (1 - δ) * Real.exp (canonicalWindow δ) := by
    rw [he]
    nlinarith [sq_nonneg δ]
  exact window_bounds_of_unit_mass_tail k (canonicalWindow δ) δ hk hki hmass hexp ht ht'

end HVRPhysicalKernelCanonicalWindow
