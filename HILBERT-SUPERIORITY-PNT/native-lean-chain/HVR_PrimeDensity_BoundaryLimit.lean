import HVR_PrimeDensity_BoundaryLink
import Mathlib.Topology.UniformSpace.HeineCantor

noncomputable section
open Filter
open scoped Topology
open HVRCorrectionBoundaryLimit HVRPrimeZetaSplit
open HVRPrimeDensityLaplace HVRSmoothingBoundaryExtension HVRPrimeDensityBoundaryLink

/-!
Candidate pointwise and compact-uniform right boundary limits for the actual
prime-density Laplace transform. Fourier inversion and PNT are not claimed.
This file has not been compiled; no local Lean execution occurred.
-/
namespace HVRPrimeDensityBoundaryLimit

/-- Approach any imaginary-axis point from the right along a horizontal ray. -/
theorem primeDensityLaplace_tendsto_right_boundary (t : ℝ) :
    Tendsto (fun a : ℝ => primeDensityLaplace ((a : ℂ) + (t : ℂ) * Complex.I))
      (𝓝[>] (0 : ℝ)) (𝓝 (patchedShift ((t : ℂ) * Complex.I))) := by
  have hline : Tendsto (fun a : ℝ => (a : ℂ) + (t : ℂ) * Complex.I)
      (𝓝[>] (0 : ℝ)) (𝓝 ((t : ℂ) * Complex.I)) := by
    have hc : ContinuousAt (fun a : ℝ => (a : ℂ) + (t : ℂ) * Complex.I) 0 := by
      fun_prop
    simpa only [Complex.ofReal_zero, zero_add] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hlimit := (patchedShift_continuousAt_imaginary t).tendsto.comp hline
  apply hlimit.congr'
  filter_upwards [self_mem_nhdsWithin] with a ha
  have ha' : 0 < a := ha
  have hsigma : 1 < 1 + a := by linarith
  have hpoint : zetaPoint (1 + a) t - 1 = (a : ℂ) + (t : ℂ) * Complex.I := by
    simp only [zetaPoint, Complex.ofReal_add, Complex.ofReal_one]
    ring
  simpa only [Function.comp_def, hpoint] using
    (primeDensityLaplace_eq_patchedShift (1 + a) t hsigma).symm

/-- The same boundary value along the previously audited reciprocal sequence. -/
theorem primeDensityLaplace_boundaryEps_tendsto (t : ℝ) :
    Tendsto (fun n : ℕ => primeDensityLaplace
      ((boundaryEps n : ℂ) + (t : ℂ) * Complex.I)) atTop
      (𝓝 (patchedShift ((t : ℂ) * Complex.I))) := by
  have heps : Tendsto boundaryEps atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · exact boundaryEps_tendsto
    · filter_upwards [] with n
      exact boundaryEps_pos n
  exact (primeDensityLaplace_tendsto_right_boundary t).comp heps

/-- Uniform approach on any compact frequency set. The compactness argument
uses continuity at the boundary points, with no global continuity premise. -/
theorem primeDensityLaplace_uniform_on_compact (K : Set ℝ) (hK : IsCompact K)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a t : ℝ, 0 < a → a < δ → t ∈ K →
      dist (primeDensityLaplace ((a : ℂ) + (t : ℂ) * Complex.I))
        (patchedShift ((t : ℂ) * Complex.I)) < ε := by
  let line : ℝ → ℂ := fun t => (t : ℂ) * Complex.I
  let Kline : Set ℂ := line '' K
  have hline : Continuous line := by dsimp [line]; fun_prop
  have hcompact : IsCompact Kline := hK.image hline
  have hcontinuous : ∀ z ∈ Kline, ContinuousAt patchedShift z := by
    intro z hz
    obtain ⟨t, ht, rfl⟩ := hz
    exact patchedShift_continuousAt_imaginary t
  have hnear : {p : ℂ × ℂ | p.1 ∈ Kline →
      dist (patchedShift p.1) (patchedShift p.2) < ε} ∈ uniformity ℂ := by
    exact hcompact.uniformContinuousAt_of_continuousAt patchedShift hcontinuous
      (Metric.dist_mem_uniformity hε)
  obtain ⟨δ, hδ, hclose⟩ := Metric.mem_uniformity_dist.mp hnear
  refine ⟨δ, hδ, ?_⟩
  intro a t ha had ht
  have hdist : dist ((t : ℂ) * Complex.I)
      ((a : ℂ) + (t : ℂ) * Complex.I) < δ := by
    have heq : (t : ℂ) * Complex.I - ((a : ℂ) + (t : ℂ) * Complex.I) = -(a : ℂ) := by ring
    simp only [dist_eq_norm, heq, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos ha]
    exact had
  have hbase : ((t : ℂ) * Complex.I) ∈ Kline := by
    exact ⟨t, ht, rfl⟩
  have hbound := hclose hdist hbase
  have hsigma : 1 < 1 + a := by linarith
  have hpoint : zetaPoint (1 + a) t - 1 = (a : ℂ) + (t : ℂ) * Complex.I := by
    simp only [zetaPoint, Complex.ofReal_add, Complex.ofReal_one]
    ring
  have hid : primeDensityLaplace ((a : ℂ) + (t : ℂ) * Complex.I) =
      patchedShift ((a : ℂ) + (t : ℂ) * Complex.I) := by
    simpa only [hpoint] using primeDensityLaplace_eq_patchedShift (1 + a) t hsigma
  rw [hid, dist_comm]
  exact hbound

end HVRPrimeDensityBoundaryLimit
