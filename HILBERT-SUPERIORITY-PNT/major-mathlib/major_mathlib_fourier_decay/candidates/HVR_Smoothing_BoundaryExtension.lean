import HVR_Smoothing_PoleGlue
import HVR_PrimeCount_LogSubstitution

noncomputable section
open Filter
open scoped Topology
open HVRCorrectionBoundaryLimit HVRZetaBoundarySequence
open HVRPrimeZetaSplit HVRPrimeCountLogSubstitution
open HVRSmoothingAnalyticGerms

/-!
Candidate continuity and gluing for the analytic boundary expression of the
actual pole-subtracted prime exponential integral. It does not establish the
subtraction-inside-integral Laplace identity, uniform boundary convergence,
Fourier inversion, or PNT. No local Lean execution was performed.
-/
namespace HVRSmoothingBoundaryExtension

/-- Fill the removable pole at the origin using the audited pole germ. -/
def patchedShift (z : ℂ) : ℂ :=
  if z = 0 then poleRegularPart 0 else regularPartAt (1 + z)

/-- The patched function agrees locally with the pole germ, including zero. -/
theorem patchedShift_eventuallyEq_pole :
    patchedShift =ᶠ[𝓝 (0 : ℂ)] poleRegularPart := by
  have hp : ∀ᶠ z : ℂ in 𝓝 (0 : ℂ),
      z ≠ 0 → poleRegularPart z = regularPartAt (1 + z) := by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using
      (eventually_nhdsWithin_iff.mp poleRegularPart_eventuallyEq_raw)
  filter_upwards [hp] with z hz
  by_cases h : z = 0
  · subst z
    simp [patchedShift]
  · simp only [patchedShift, if_neg h]
    exact (hz h).symm

theorem patchedShift_continuousAt_zero : ContinuousAt patchedShift 0 :=
  poleRegularPart_differentiableAt_zero.continuousAt.congr_of_eventuallyEq
    patchedShift_eventuallyEq_pole

/-- The patched germ is continuous at every point of the imaginary axis. -/
theorem patchedShift_continuousAt_imaginary (t : ℝ) :
    ContinuousAt patchedShift ((t : ℂ) * Complex.I) := by
  by_cases ht : t = 0
  · subst t
    simpa only [Complex.ofReal_zero, zero_mul] using patchedShift_continuousAt_zero
  · have hti : ((t : ℂ) * Complex.I) ≠ 0 := by
      have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht
      exact mul_ne_zero ht' Complex.I_ne_zero
    have hc : ContinuousAt (fun z : ℂ => regularPartAt (1 + z))
        ((t : ℂ) * Complex.I) := by
      have hg : ContinuousAt regularPartAt (1 + (t : ℂ) * Complex.I) := by
        simpa only [boundaryPoint] using
          (regularPartAt_differentiableAt_boundary t ht).continuousAt
      have hshift : ContinuousAt (fun z : ℂ => 1 + z) ((t : ℂ) * Complex.I) := by
        fun_prop
      exact hg.comp (f := fun z : ℂ => 1 + z) hshift
    apply hc.congr_of_eventuallyEq
    filter_upwards [eventually_ne_nhds hti] with z hz
    simp only [patchedShift, if_neg hz]

/-- Continuous boundary values on the whole real frequency line. -/
theorem patchedShift_continuous_boundary :
    Continuous (fun t : ℝ => patchedShift ((t : ℂ) * Complex.I)) := by
  rw [continuous_iff_continuousAt]
  intro t
  have hline : ContinuousAt (fun u : ℝ => (u : ℂ) * Complex.I) t := by fun_prop
  exact (patchedShift_continuousAt_imaginary t).comp
    (f := fun u : ℝ => (u : ℂ) * Complex.I) hline

/-- The audited prime exponential integral has the patched value throughout
its open right half-plane. -/
theorem exp_integral_sub_pole_eq_patchedShift
    (sigma t : ℝ) (hsigma : 1 < sigma) :
    (∫ u : ℝ in Set.Ioi 0,
      HVRPrimeCountMellin.primeTheta (Real.exp u) *
        Complex.exp (-(zetaPoint sigma t) * (u : ℂ))) -
      (zetaPoint sigma t - 1)⁻¹ = patchedShift (zetaPoint sigma t - 1) := by
  rw [exp_integral_sub_pole_eq_regularPartAt sigma t hsigma]
  have hne : zetaPoint sigma t - 1 ≠ 0 := by
    intro h
    have hre : (zetaPoint sigma t - 1).re = sigma - 1 := by simp [zetaPoint]
    rw [h] at hre
    simp only [Complex.zero_re] at hre
    linarith
  simp only [patchedShift, if_neg hne]
  congr 1
  ring

end HVRSmoothingBoundaryExtension
