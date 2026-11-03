import HVR_PrimeDensity_ConcentratedSqueeze
import Mathlib.Analysis.SpecialFunctions.Log.Basic

noncomputable section
open Filter MeasureTheory
open scoped Topology
open HVRPrimeLogDensity HVRMonotoneNormalization
open HVRPrimeDensityConcentratedSqueeze

/-!
Candidate adapter to the actual Chebyshev theta-ratio endpoint. The second
theorem is conditional on the explicit concentrated-kernel and convolution
limits below. It does not prove kernel existence, the convolution limits,
route independence, or the unconditional prime number theorem. No local Lean
run was performed.
-/
namespace HVRPrimeDensityPNTConditional

/-- Transfer convergence in logarithmic coordinates to the theta ratio. -/
theorem theta_ratio_tendsto_one_of_density
    (hg : Tendsto logPrimeDensity atTop (nhds 1)) :
    Tendsto (fun x : ℝ => Chebyshev.theta x / x) atTop (nhds 1) := by
  have hcomp : Tendsto (fun x : ℝ => logPrimeDensity (Real.log x)) atTop (nhds 1) :=
    hg.comp Real.tendsto_log_atTop
  apply hcomp.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  simp only [logPrimeDensity, normalizedMass, logPrimeMass, Real.exp_neg,
    Real.exp_log hx, div_eq_mul_inv, mul_comm]

/-- Conditional exact theta-ratio endpoint. The displayed quantified kernel
conditions are all explicit and remain to be established for the HVR route. -/
theorem theta_ratio_tendsto_one_of_concentrated_smoothing
    (hkernel : ∀ δ : ℝ, 0 < δ → δ < 1 →
      ∃ (h : ℝ) (k : ℝ → ℝ),
        (∀ v : ℝ, 0 ≤ k v) ∧ IntegrableOn k Set.univ volume ∧
        (1 - δ) * Real.exp h ≤ (∫ v : ℝ in Set.Icc 0 h, k v) ∧
        Real.exp h * (∫ v : ℝ in Set.Icc 0 h, k v) ≤ 1 + δ ∧
        (∫ v : ℝ in (Set.Icc 0 h)ᶜ, k v) ≤ δ ∧
        Tendsto (forwardSmooth k) atTop (nhds 1) ∧
        Tendsto (backwardSmooth k) atTop (nhds 1)) :
    Tendsto (fun x : ℝ => Chebyshev.theta x / x) atTop (nhds 1) := by
  exact theta_ratio_tendsto_one_of_density
    (primeDensity_tendsto_of_concentrated_smoothing hkernel)

end HVRPrimeDensityPNTConditional
