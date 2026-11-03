import HVR_PhysicalKernel_PositiveMass
import HVR_PrimeDensity_ConcentratedSqueeze

noncomputable section
open MeasureTheory
open HVRPhysicalKernelCandidate HVRPrimeDensityConcentratedSqueeze

/-!
Candidate support for kernel concentration. The normalized physical kernel is
integrable. The numerical window conditions follow from a unit total mass, a
small complement integral and a small exponential factor. Construction of a
bandlimited kernel with such a tail is an explicit remaining task. No Lean has
been executed locally.
-/
namespace HVRPhysicalKernelWindowAlgebra

theorem normalizedKernel_integrable (w : ℝ) (hw : 0 < w) :
    Integrable (normalizedKernel w hw) volume := by
  unfold normalizedKernel
  exact (rawKernel_integrable w hw).div_const (mass w hw)

/-- This lemma discharges only the numeric window requirements; it assumes the
unit mass and a quantified tail estimate for the specific kernel. -/
theorem window_bounds_of_unit_mass_tail (k : ℝ → ℝ) (h δ : ℝ)
    (hk : ∀ x, 0 ≤ k x) (hki : IntegrableOn k Set.univ volume)
    (hmass : (∫ x : ℝ in Set.univ, k x) = 1)
    (hexp : Real.exp h ≤ 1 + δ)
    (htail : (∫ x : ℝ in (Set.Icc 0 h)ᶜ, k x) ≤ δ)
    (htail' : (∫ x : ℝ in (Set.Icc 0 h)ᶜ, k x) ≤
      1 - (1 - δ) * Real.exp h) :
    (1 - δ) * Real.exp h ≤ (∫ x : ℝ in Set.Icc 0 h, k x) ∧
    Real.exp h * (∫ x : ℝ in Set.Icc 0 h, k x) ≤ 1 + δ ∧
    (∫ x : ℝ in (Set.Icc 0 h)ᶜ, k x) ≤ δ := by
  have hsplit := integral_split_window k h hki
  have hnonneg : 0 ≤ (∫ x : ℝ in (Set.Icc 0 h)ᶜ, k x) := by
    apply integral_nonneg
    intro x
    exact hk x
  have hwindow : (∫ x : ℝ in Set.Icc 0 h, k x) ≤ 1 := by
    linarith
  have hscaled := mul_le_mul_of_nonneg_left hwindow (le_of_lt (Real.exp_pos h))
  constructor
  · linarith
  constructor
  · linarith
  · exact htail

end HVRPhysicalKernelWindowAlgebra
